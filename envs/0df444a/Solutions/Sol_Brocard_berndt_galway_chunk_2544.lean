-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2544
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:01:38.226595+00:00
-- url     : https://prove2.me/submissions/87126699-ae77-48fc-840b-4f1365038a71

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 457374100 ≤ n < 457553956 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 457375350 1250 457374100 457374133
    0x2070b010e0115030506062b06050f06030609090a1a161e05130314030304020f0618300a051603020d0204050618090c090f0705030f040507080f0f 64
    0x1d0480d01c08400940f081c0183c480d00b1002011301410703555000e401085600d0b1502d0300000d8802c03e240c660400e144034449025900e42c215545640920300074040c0407241350160740d070b034410b99500081c103580c8804903949945e82030f810a0142d500c01058002000c03110051089000c2d43c0510450708070050040e900504003003522412550401c52141240004090420ba84078030b01070510b01c50b0210102d40c10548130f545e8980e600102c540c807018144c2c400300410080d882c4c01e001480b0100c8058400518120140d100320550f8800542d0041c05500c1943e400002d240010b1000c6400c5400821803c603038803540c0c0307451603c1e5010b100d03040c0c07024810070081080586068854a003140d90081549005610036424003002c1d01d0000c008030ba103c2c0d40d28054a910b00c1061038003030301c500c8290f8082c200351407003031040140c1e80344049c0c007104e54000504100404a41c2003003c503600301c1d2480e52001031940d9030f881e005140c40b185410003d12070180900f080054500003071180c161400d41019951491100c05150 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 457376600 1250 457375350 457375379
    0x1b1c05060f040b07050f0d0b062506110405030a030c021518030606120d030b1906050409151505091914010201060b0a0801060c0c0e130b06010c03140a18080102070b01 73
    0x1b2448000800c007040c0c01200d10b5210404202028010900b000404c400500704250021010b0740c22030500d6050300104845403007990b41441094031140c3c20305042a01003a6900641e01000f070a00103046034403001c0d035880c0e6034110301009001d41060707902c64003010030103001c0c107400042c07c1c064444ca82c08034005140c80340e0708584800402c0c0050094008482e4220090000c00030284e1b00122100070110070302c2c0c00c000b500380180c5142d0721815a96840c00c4a62011513a0701782c7d9440560400040170301484200da039401340d0301da4840c6011502c9584120003c0c00500803100d14000c103005505000035000c04a80b4040c0140c0d000741c001300240c0796100c0f024070451046240980008408200601c0b030503000745d1000c8c2000e4040e10300c50040544518021301c0d4040151802d900c054055031000040106010b040ca922413001e2a003c003038a1116500a0b020214800c612145054041160780f05a032250400036038070300032507030701005c43e90362524618000c0d40001c40913030b8480101e40012070701c3d80380d40a0a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 457377850 1250 457376600 457376617
    0x1080903070813171b1009090603050105011a0903070306020714010e100e1b091801020d020717070209011404180f05070e01080726010c11060601021b1c05060f040b0705 74
    0x20080c00c0c0d01708000c185109501940e081c8010114007043c51070842c4103480155101e01c2c000110b42d410080f84d00101d1845c5110111204000c00091260f0f440105101c1704481c0d01210160b152075242c43d0908800883d1082d01c2000c1d860112020640c07900000c034102c150041c60301c20008408020221901c805040c000340555680141002410b410642c0e0320a0340800d80001c2d498004090b588500d0030381e4080d0040c40c198a4010484c54144540c0300452100f80c00030b5244203107480c3e081da002c05e011003030504c14800d00507280d00100919031035603000300c11800741d81004500022004d1420100311002c8032000d0303640d84512100442c4c1e07400b050308602d0503240000000e08280303280800341003065541f0303109108041390030304070381c651a00c09008074405503140342c42d1083c10401307003008030f46030080c0102284e0465105081003000202e880f040411403141c152000040140c8510410418225848000301b0500c105002c003c3d81440b810f0080b409184901070b80c1c07140e03403a000c1e0102c59030b0040800 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 457379100 1250 457377850 457377883
    0x1209030f0b18030c15060a06120c1e090905060a030f150207020a1215050c340803220812060409120203070c0b0406020703020108090307081317 63
    0x24110042a491404680e0203018a00c4440c5108080c02d020b9003190409121201d00b07600c22185000844041103840e0b52152040d25005040c41c41d000703004203852550603650201e142e648001c65002803040582d5140c1100800c03029001d1508000010542401ca12030411894a041c000c10400d01e0f240c482282140e811900c0310030207000540306c05e40f0351840d0175101242c40c0d40c200003110040e01c0d89030000c0000d000344c5008040400752810101c82d0100140d1480b041c40d882d0404105404508000751400c1c103600343c14030001002000c100e11020389156462403180403059480c0402c100610300214821010940f1001c01a2246407622010301c080300002001075406101c450b05000e415032640b9800800100085086400f640301c01c1032051400025100603040002c01d58184000c09001100801000464919043c03400034002d48031240c5000082c10040c583c808240400000c00640c1d2410303800202c1c590707031014083c01100485c0d905100307014041d03002c07041c2e0a41034040440c4900100e0701051 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 457380350 1250 457379100 457379123
    0xf0c0f04140613060504110403020405070201151413050a0501290a320a031518021308010f020702010807020d080c0309010e0f0601050906100203040603021303080d09120903 76
    0x2044480070303c0300d0201c0211a5500f400040d180d66500415030220b50305a1201d55480c154014001920300c0144030b2029a13062040e801280300c071154000c411501a0f1a015504440250015076501000034010750100e08100a1080071f05060380203504807444200f003038180e0400110a03034211840c240c42500501014408401c85c14043c1c6503080d20321000d00500e9010101e82000c00300058510031007540b1120b008a510080990544640070541c2c000003a00c0710014580320b454416185032000d5200c440e5000301c0e01105100404074500051702880001340034004050782420000d401c9150242d00141843c1d0110b042140041041c1c00200c0d50356035402d5a070b40c3d40d280401403d0f8806055000c42d0342d41d8a40442608009104029050071803d025100307951403c0204803200344080e102074421030060000c11161500082250308540c50703400c000da19507685007050360388010641d001070180c0307800050135a10b0840b9540b2100c2c486200382000d69840d130042400300c0b2141c6e118000201401300b400d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 457381600 1250 457380350 457380361
    0x90a080f1c020303071218030206060a0807120807030c02030f0c0901091802190801140f01140603040b1005060705010219030b01120207063e070803071b050f0c0f0414 73
    0x41e0000e00300d8050108003c10781c047c035000c10032a002c40c002c00c1500140c010409001c841d282280302c600c02090040b00a0014504205180030071007611480148040c00008a1500b0580600c2481a1183c2c008055074a501c680d10091900c07120404400c61040f0440300001c540205540304a981b00d00004000c00c0300c00d5500d07403d1240310f074604003d08140042001000038061000d01802d4103004080222000905054841c07107507861044e0000e0382020a0341f0403140e126121202a2507101790405080740c0c8a4807403448080c2a50b055800c40350f001200058030750305000c0150020180341351803da20343c0b80d6401d0003070704074100c130b214104d41c1c0e00080320500b070501d9011203500505801030150742c0002c0c80403200c5c140740d00e21062284c0194920708200c0c0d0441d0415103094440b21004100410032464101c00703945d40303c0b403844010007510a0288101c04a0391924800c00c0302003043d54040100c4001340c4648020541e503401c0200710500c1150843e6540030f55060034020f511211003101da2265094070b41 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 457382850 1250 457381600 457381607
    0x14190608150910290a09080c031c050d02040e01151803031b08090604080d0206130c0b0d0b150306191503020c0a050106030606030213050f01050105090303090a080f1c02030307 77
    0x43c1040000d010140f030070142600c904040108059117850302c421025a107002d0042d42071982ca0104584250026503502c912401c01000d000303482c100c1480e000f641d90303030402100030080c05650044685051100008510f08079044000b20080b00692951801c0c540240c8000606510030b000080001d1015182d00b88a40b80020349640352920403d5002e042910072004a8170b6138200764410090b0340d2182d0210005203405003c0035400ca0101c0c845488500700c4d94807207140201451191a14100c8006054021240c1c030b035000d002c1100700103100f58560161003021140c0c9403c25544a88512501145064104050384141044641040d1003100e918103041c3c060740250454051414a402150408170000701c0078440e0501851042e0b200082c0c8a0441c0113120544428074002503c83d45048280a0700400c2c1d0110a070442d0b5091078400d40d00e0b0614800710741140501c1400582018415070089861100412062126140b41c030480d001540c03410501b01884d400c000810300903070810404101050720 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 457384100 1250 457382850 457382879
    0x20a110d020c0112060806040b070311031b0a05090d150501230d0f0b010e04050601060813020f301207021008040c0e0a0b040c140414190608150910 65
    0x2130f41800086003540d881c50b040c14003500329022203d009c1080c0401c00801e4041c45108886200f080300e4a0a40c03a0000d4803a804010000c21942c102f000440c40c4c074980c900c282d0440d0300130038000c0c22035554501e0516203010700e104041c0041c601c1e903042c4800464914040781d852100b51604e43c00d4501b84008010501070440001d2800f030707807000d9006629001282800060714000c01140c07000c4c0d0058179260034428142403041e00101c0c10400324500340401e82c10344507412081641c044800c07203012a0700100090702c14210a541003800d1001e02911007100d01c11207036091a00c421a01501c002c00c02d400c020250601c90044001d5121a011444d90815849210340d00d40c02403003170149041c04c641790b50844241b00c804481d0170840c81d49540a0b8245802d00d802203480200d0203082a41c03508005245014150241e40520303078420b012255a1440d5aa84968002c0c030070181c241424012912244001e0a40d0000c441d500380c5410b1990035190a810003e40982c40351410201d4920a1401e01891390380d890b0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 457385350 1250 457384100 457384127
    0x307030c06060b0307110c100c02040507020f061006080a090305030f0c041a09040c08040512160f0b07090b0c030f090315070e0307050603010e130c1701020a110d020c01 74
    0xd560302030224110320908025070041175603440b403500080215599500c2c01c0011010f031805004180552251240c02c0350481b11850360450b0080340d2640e51690407460142c5415010082e4030907a4140700707000340010384a0090710060354515500d9500c00d4550000d0341c1840380018006101000090031000c155111950403d5a02e891140380030f40d1000c5191708420004620045112700050803501890716120b0070b80c0c503100303c1c01e01041500d0180c9480f5201c40310b00d0303d0343d00b0860001500d03840300200d01040b603080c164081055a00c3c8510b50400c000703e01070459060010410802e00030031550045002e59006008841c001d42c03805004041c0a00f040c0c00088840360188aa00702c49041485007030102403158805503541000004100205858845103a10090181e0030800051080000307405880e03910010039007858007000300b6440c2040390440306a100d050502c5014900d91203000041d0020411401d05c1c4da40e060382c06141120380341d00d0f5003581c9100405644480c500c0e001550144400040740b0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 457386600 1250 457385350 457385363
    0x90a0f0206071203050f06011b0210020703080403080a170408070f0317090c150903281401050a05100b16060e03040f080d05040f0b030408040f0b0d0e01020a020307030c 74
    0x7a940d03580ea0f060103540030301d80c5011a44030010400c841d10400c840d154018800d10b401e0304522201860340f0700e4080f0351a4081d021708400381604040318020400d030300086600002540d0f03161794900b44a10765403c001a4580003442c0c003220187d40d240c8000c00d41d805280c0003004503140c40c00c00c0d43c401c03114130111641103042c4012400826a07191030300102c14851201400a000d00c141c1c4042004014501069104000712084c09001d805840000c2e1510465403425110500c00c0c40034040d082d03c501c02108010410a80d1004880540344190001c07030242041000601050b11038004025004150f0700600640f1042442600c1c00c02c59285181000b240c01110002500c1060740d00e158150352050300b000790709440c028000c011580040000b1608003402c3d01d446400c060410140d06000d06003131055501010303000c4003007014403c0700001c0340c00030098080d080c20005e40d2107003201030079000103420150051a007048001c51403030600031240c021400ba40903525041c015a02554034410000e03003511710 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 457387850 1250 457386600 457386607
    0x7080a2301030501020a0f14222111061c02091315031509020d261603080f15040c0309080d0902150f070b04111905011403090a0f0206 59
    0x204688030011034065802000050303a210040f00c00504444010300401c400c04c04400d0a0410b1800c02500380c80d43c1111000400d0000b01040a110340f140c106604070300311b08408203a1103401c0c030390405040301d602481a8622034128100e00d041280f00c2c01140011005030002061011102c0c6043c3e000348400b0500400d4140307045240341c140c404588180003410b41c19070b081c0d203060080c4070110a12481001c100101030244101607030105000303405c021401013401c09015405402d09a0491000c3c0140100700002601d60702503000020300c99521290a80100c0e201c0c0d00850005201d0942051080220a50701c0207148413000920000f44130452491042503a122108c0c40000c2e500f01c0200003001a4020202c2c001d4054010020541d2b44280c000c0300e00e5a0402c0602200c04e420019101400e070040043c00c0142c4c0e0710b0422481903216084000d5200b1810f0113002c250702c04040f070000c160f030000e0307030380b001c80f0b00081054020612056582c6411a0311520848000502c903440d12030030688003401c12802c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 457389100 1250 457387850 457387901
    0xc12040b070311160f1d010b090f0a1d0a0b040b03070312020307050303012301020f0a0809010c021309110a03112809020306041a0105070f0c170109060c030507080a 72
    0x1901503017500480c1045103111001c118181e02d010820000c2c00501c0c2e5001c185524205400010340b081e41950b40c054060408001680d98401900400404000000034000c41039200401c40840080b05d001c031405180240c86051402e1900c540215100f0240c010035025045807200100450070189000461208100d4400041d1083c80614000c06641500c4100040c0c3da100c00000000038096450444d4010031120f240103100003120f4400b16003000203142d80b16901d000403502c00c2d48c1000083d4001d08000e41071a15181280c2c4040804e601400d48070404013038103130030000718030806c0c800a4201e4212030509490351500c0d001a03c00045080c01c40e8103400c9000c40800100c50407075000c03407241c0b0307404010400182424020507900710300e40502d0030358100f00e940020302540a02e42d4081e202012800d001c104224050112501400e203803c42003a25000d000c0800c0d018100b56401219424100204e42c80c2c0c0500a000f918002d0070a83c03296042079442d15410300040080340742801c3e01801c10f030a90070 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 457390350 1250 457389100 457389133
    0x9040e01060b0d0e0c060a080c130b0a080405010f2009130507080f0a0228181e1e0501120f0c050c2a100201061a0c12040b070311 57
    0x85440c03c2103c0494020b000081e01c0c1d040c00e0f08000c80030300580e810000d90083d0703688803035031551010076804813070785550303050740022044001600a002256400a078145003140c00c0240d242c030587c803c00c024440d070503070041510107407a88402c0002c145c45040d40400c04101b0050068070039a440944032a00499880d0400340640d4020f070340d6100818034036418070001c50120901a43c1c8071078048010761401014611402c204907007032400c0a004210844050003544c03180c1c00440030410804945411161101c034030f0000802c00c00c041c0b40c08507030159400103400401558210000540854101080e440c0000550f1400680d0002d82642c942d00d1643c8015407016110b9500d8421160355226210002011864940300d1010307a0740b060000d8641d080281064201e11450028000352400110199107007010303805490301360000701440d0b0358a00309840d4411000c019249243c0507100301c88032860318080903061441140200c0d50841c50801015011900482d41c140ba01051f581c1141c1200020b42001c1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 457391600 1250 457390350 457390357
    0xc300a0e04140405071a030615090405010b0c10141b16030509011403040b1503280c23060f1b010c020f0111041502010b152d09040e01060b 61
    0x48015081e5010f110910004210910250906001d070040c41700503100001603600004000c50310603181d81041c0e0200c06c10b0300003958202030b8003070404d000342d5271501001803140c0c00c95000402c0504c01d00d084a50405114011403103110b01c1d0a000207016182c0311103141e6582080103280051150811101d9548401748107245138103806655980d4513251500c00041c0f1100424025000100341801400041864000b143d41c1000300c102c1c80c010000314140220b03040082800b50b00751106840b4000e142d203001c2d03642c0c40c082c0075485644003001c0c280c1c4072400d6014540c2c1c08203840025903181c4082084d1414050024001501201c00c0705007000380c80352111601c0c4407108880744140c1d440711000380703042d601013080c40594441d0000034043e02418603080741a5009510482d69002e0003988451071488c000e44c8140250034011300342e0440c0450500c80c2c1505640a140c03120049070750b640140c82d42401c0030400450708002a0f200074585800c1c50100030140c2186005240f140d540e031000024201500c0c0001c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 457392850 1250 457391600 457391621
    0x14030a0905033f070c150c03060302030d0201050c0d1505040f15090c020c04021b01090503030907081c05070c150908060a020c03030f04030c020a0306020c300a0e04 72
    0xc0008500090041c01c44154148226000d4080f000b50503c1d40f2003400c458841c1d0203200741c03800040c501c003142008181c1a01a000b0001e8031031503c6039101009916411075410343e0f000b41c04507105825014003c07030883e81c048400c8200000144582003c0103042d80001403030240c3c15200c0000c1700e032a80001070445005440c080046079480001000e00281c9248802c020828190100115401924080d4840542c138003114032840d800601c055050584000090030024903400070001c41c140341c9400c950781d40c0251001c0c040c034420010000340c00c1000082c4080c4020003d54101d440c2c43c01000150b0b400e405c0580100c81c440194103000c00c1804a002c000007040f50340e561805202843c100200d410200040c0003042c00900401110010aa000040f80c0e0040c41050684d80e25517034906040710005071000300258003d400e03010001c01c0c0714198000d0103c62800206440340c50300827442d43e2094260520131064a152801218001c000c800406000c201400d401c00c502c1407101d10001504540f00240c4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 457394100 1250 457392850 457392877
    0x402011103120f22050d120207060207051e0606030d110a0b091b0102031305010507151404120f140c100905010606031b17061314060118050114030a090503 68
    0x4020341021854442803041136040f0020130390702065103c0b00d46810003030803004140304480c0b008925440066040b5401c4507001034085488402c54034201d0384032a03c0d008025410030b0f00f50041d10300c555021845500880c0000c000300401d0144560603070f501015112801098010703a0303005070105d00301e2405103214155031005084c9110022040c0a10350020810070b504651080c0328800801c3c4603082d40009894007420495242c4500b03180c00604644c050a94224407400e00901103e1f00d002c10403d20b000314850510001452154001115503941d404010400a00d40429040b0300e00c024000034400e4400040a440c002005a608201960101c0c1c81c12280d5a64443e003c21500368035218448100c40940d40701031004c0a00c2500609840000c0c01c800c001c1a5040042101540e5200c090500c45461001c00d020126070442c03070090910044031140d020854200d0711580c0d400300c403540d6505543c070503160351a0b14441c184020711140c2004091500c0c49554541c0c140209008001904e641035103080b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 457395350 1250 457394100 457394131
    0xd02060c011e020a0e09090f0d0c03080a020304081c0f1e0609020405060406031a0a06080a0b03011b030b030f031c06080109020d030c030201110c0304140612040201110312 75
    0x811180300c0010b40015208041c03041c810902c0d0254450b5900301900c40403607405a26890300040e0504161800e000365000d80720300300000c907207550403a14400c02c685c02500c841c0d07030130b50728601c40e0340c2a844101c0d4000c01514040010304414070f154840120b03070b50f030b00d00400500c01d0005c0d00140c048480000018008100103a1f6100002c0f029015010103403083e26002c0d820249404041001d40c040c4d40100300130f06840314140d06191000b410800903003c0024440b844035950343c0f4000d4505030007922141c22003401d2060204503400c0500400507800140482d0751084048102c5c21401000044222541402840300d0044208020000350450508150070525030280303d0160408032030840e0b1103a90181d0405000d01c02681c0c0f501c80c03002400760035050000b14100e451608034014100701004503e020000b04006405101c0000900103544400d030318425209400b81c1000381714000c41c901130031f4000c00b080018005512a00b603007090701e44490100c1b0b003404070601c1c4052080300121480101c0d110341c0c6 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 457396600 1250 457395350 457395371
    0x30a1a0a0b03030307030b150909070503042105030405012009120309030f1c170c030a140103080d0c03060e0417070b0c0306101701140d02040905030702090601090e0f060d02060c01 79
    0x408c201c3d9000f0b0526110185031481c0e410104040100041101c0c0c02e00c08007200082c284064100c40072821888034101c2d05241c110008058241d800a50303003918913603c1c20429005420305c08040c480c40110790351441d800d00300d403441042900d00344601c1303040c0103010600c8289855201004200c6903040b03000e02402451b0f5100b890352981444103d100c10400c06414130019800c124003001f560000800380110703175a651407049038400380003002c0003240c620f4a088000402e00c00724401501c0003440d0481d0500515110031030480542d070041c040c049504001402040000380d050507014880c0142d0030382c103400c105041d240c48080003412118548105800000c120040c07910440c4641030714141c2c00c1c05075098156103c0040700c0001400707850008502400c507841999181710b40c0b24042c1c0e0b8010003d00065040e440c00303548035040444104c1c090003201c0007103512503000311081e50aa4201d54903060380c60342d520484c5860300c0000b410040c1c20451440801000d030321174070010306110500000200c0c080805 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 457397850 1250 457396600 457396609
    0x30108010c03110301030305120703180318080304141201060312030b030705011e030b010e0d0302150a05061e01092303060a02180d080405210c030a1a0a0b03030307030b 74
    0x1c020f11a4a0b00781003005000080d004800d44030b0589031160070800903921400143d0041140d540d0215016100c224060101039002015940e00c1000000440d8240d50700c9900f6a542d0060b0b02444140e40480700cbc0650040c244000c007070041d02e490700c001040c40c691f652111b842c80e0041203205400070351200f0600956080c2007006000034002803915003e0054842d40104c007121441110000300340c0c0300d030f00c80c560f80ea100da071070b2455445000704020122a40d900d0069519205400281400710261001500140301031080c203115803c0500703410302d074488440e05a8401040415400c0c1400b50202001c16107860b00c03048180559010610700b1451100342c410146803501c020400c804050041142514060a00042c01120f440a450f4040f400c1505e20705030b8903074012a08029003210340c6c3c0c2141042ca0459585046110174070000382d85410f0410000d145d1180d42c0803101030030f203601d0740b5910070610b1003000c50307640e003c0c40190001480304580d100090641d3300c11f42d04c440009072607100040c0307141341 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 457399100 1250 457397850 457397861
    0x621030705070b160204091b080309090a15031203060b0d02091201060f180603080f03180607021e210408010606110a12050d020c0115150e040e0a0602030108010c03 72
    0xb814082d5041458600c1300498080c6152002800f494651b50200104400c02111032551410f0340c40c1400f9003030f254036006641e0f03040b0f038038403500c41c144e02404540d1085070342c0b1421781c1c1400800300d80743e101811522110280ea040301c403c0801c140c1d07541e2001504100ad600a40a4491100005070369404490100036881c420b905242c02a640f4105040028482e044041c400300c4400d010b40030010302c00704219000512059101a0001c8000036070050441c88440046101d0640b80200c0d40c88135549a068568920040b284140564080d10210300702c242150081c400c000190320840307101c0300120f100e0305040d585d034084281508801007010300444000380106d6000c0c016a180c003542c00742c02105215a100c1c0e603000701030551280d00da08141000d200d20100c98000080110a541d9010b610605a00a00000000400c40d240340040402c40e41b41c803403c5040c0d00c000e55906c07400142501c0e01000000c0c019402c00c60380301d10544081400040803800078500810b030600000800c04031040b0041c00750350 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 457400350 1250 457399100 457399109
    0x2190c17031611030c0a090906051608070513120f06050c070302030405040908091207060305180c0f060d060602100b04020f07030e060412080a0e01020c01020c09062103070507 77
    0x30414800b8200404030000300440c81c507000500038900d1001c00d00824242100303131031644d400400200c0c011035110704070b8000da4079040c4240020000740d5100c2c0e445541d000c44100ca40800a8400004100e503d403041c40503250b518250404051101ea482207040c81c43c18036040e080342d1160780c040340c0d030050040301d02c242039000c640c1c080d0452500c139290364001c0d1030748a2409140d100b02c1c3d8079000326040c4580842601d5001402415502d052005110815507440c1d40f440703103a00113400c0c000029a0710015840c100c4450341108010103078609a1020040340500030094241c04c440148150818100c85000e0302d4024185038025001758100c40c40c401c1c3c299480c007640706000d14010040031041740c580034100c8040507010f103880500c0c2d003541d100164442c0b04560200050241812501c814000311034001c0080d080c0355252102d000c41a5001640c5aa4606068a0240e080720007040780c942070601146038050300050070702c81100203000200d5080d12441e1600c01c120350022071554100102003141d04042c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 457401600 1250 457400350 457400353
    0xe3106050a02092d030f0d030e01020c0105010b0d0b010302090105040905190f0b0301140c03010e07020304030c03150b01092709020607030906080916120204021201090c09090b06040603090302190c17 87
    0x26404202c405603100141f02d006420151b0320681b013103002c1000e606450070301e03107800700900240d659150182d0464020400c1402240d10b002116001507011b03200300c400e00310041c1c4842d810a4a0048180c0040c600184400c86043c240500e0b086005003511489002000c024000118402c0764004d16013141d000c0c3c42c016540c0060172050204440c0c0030b41c10703641100d5031254090340d1980d034001c041f41540901e500040c00000840004002c1240d00e9207070000c2c492111108100c03038400f4070011180507645115061030b41c0218900000c0f00511098100780140c903480003c140c044059001c030380c440e800b004050300007442035201880360507402a0a07907003290910001304011341d00c0c41e1001c0b80e200106c4c42100b6610a0311880c810440d1038607016983c140340c110941040545c0c1d070f0b040020180003040e803914006812500c02241014041c031500044103c0030b050103003410300384902039004000c9031000f942984034408152820049100c003549030035200d61081d8014514000d01c582944c01920600c0722503 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 457402850 1250 457401600 457401613
    0x18050a0b2202060f03090a150218062701020a02090901020a0f02241e0412030b0114040513021210331202040902040e3106050a02092d03 60
    0x583d07500000d80c0d01c10076014192580c2c0792910000035150001a401c01800c0403d00d0404041c0c43c05a503001e070204403610301c00d14a6040e20b003004c000a038443c07000d8010f01d00d0242e0580700035985058004520246041c01203982820a50f0000340389088201e03413290040c1e400040c0e80070060b030300907034450341ea1140c1d000510302112807541412081310421900c0b0f08522106d0006050484003824010342013174074400d40ca01a0030701c2e0070442e10a035810b0359042c01090504c2c0408856502c5410003e44100340b080e24982003504000030031480e802e05030b8850600540030700135499120840b03c0100c2c000c03e41520b082100a14011001690b0b01c0540781512094101d140203600c00156058040138800c17040c6002529103207020305001c000e000b1608003050383d6101080105500041c00c03d854040d40d5030341210070350840040001d2442503100801c0701000715030b12041000044042c1c02132600440708401c0503040502d090080348480b0095152444140300c0d81c2620a80030094800c00c1e4400388094020b0001d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 457404100 1250 457402850 457402853
    0xf0c02010507050d050a11030403080a0c0e010c061a0a2711090603060d0507080c090c25050a0609081b060702122a0c0102070f0f030618050a0b22 64
    0xf0900803007580051590301d540008030001c0082d4011744a801c1d56590a82d141c1c01c0a0500900c000ca044450303d0b4000e03e031404900150303015020309040030f481692446001111642d0b0180507180060b1610f031070540708071403055070703598129021300030b4141301e0b04003101740d0441000c200d0003289800280c80742d50711740340c0c1003018000d000b0301700c0307584d14001c3d282a80d9940310480410551408502d02510710301401001080d0028003191240302200211800c034602e458142c40e45645202d50b01d5201d0b0b035030602d01c1002c480200d0308215005094014810380310072101e903407183c8080c0c4e08060400c81d03031480d0008034050381020f20b22118001c841c5140c018141c0e1301e0301110295840c0014420100c0000c3c002ca0a0306254200c03412040c0600f040c5001003440d112030003041c5a883c20b21b44d0030240540550003004c02c1e5001c40c0003d0004956a15403000801403551f140c29000b002c903003041040441119501101061040005020781c91081d16082c01c5450605030460030301c603409116012075540c9200303000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 457405350 1250 457404100 457404107
    0xf0724210209032a0f0f09070c02010c080a09150c03210b030307050706020f06040c0b070215130603150f2d06030902090109050f040615180f0c02010507 67
    0x400a6100300c100690358070300a00040e1821340c811641c1c240691607500d0351105007160802d880b403144825110300344410340c110104040c544c03e0ba1801900003008800080c4007a10500c0002e05035401810000304034a42922205441d6110021500204407003070001c0100302114120149218028074100035160856079005000e810701c01070740751002880340e1603030180c86100d1f40443d42100c001401c0700c0d600e550f545845602d03100da038401d00c00940250740e0320ba0302c03120020603514030880e03000644100a5040560041e410380090000382c0e0030050242c268501900000010b014144041500f0680c036490004028151250003640b01d44091386e07034104219034002101d1401c02d0300c00c400c046a40103400f01c2c03049030107881505001150701d41101c200249654250780a040480e0090340e49031030b142e807070758040000e8440c1681c0c0c400503d5143c100040c00310f06554070201101c0920b50400710215601d0b81441c4851a000342990041651030000e03640d803090380d20588000c0c12240c0024001d07440e1081014 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 457406600 1250 457405350 457405397
    0x120c110109230301021b160e010b121e090f060703110406050f070503122208180a08011d151003150e010c050d1a030c040e0f0724 57
    0xb4905481ea035441c1c519590a40658110150b42c0c0c21461814981011060f6aa003a80e0007143d1840341b030b850086044040ca01c10f030390680350700d0b880701441c1c1020108103000020009081c1c0351034049080b00030320007015441c496401110f84c14010524170071011107071030070401d028041e48113051400b04803084000c0240151821507a041c03c0043d100d4890441030002c41c850301ea0000c1181c04006244821403043c0e92403180190440c1c0d80c030301e400f0611610071075490300d81440f0203010f0320014080c0c034501c1001c803000c01700d00d11400340154002d00c0c1d641b8000c0d400c0d075150f00008004c1400000141030b03110010444180608020b101c1403585051500b00e41101e0131040c00064154030400c0c070300542808080e04101d49071126000200244040c815009115802c10940c2c824854200304848800b9507500400c40c24900009003d04485000c10023000300500e0075418000d46802540740b02c15100000780080d800030010582c041610a50041081440380340d0100d00c1d405004e07202420700c543d45501c0c10318 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 457407850 1250 457406600 457406639
    0x10303030e0d0f0c03050f0d050f1506161505070203030601110601030f0f1a0112021f090902130b0c030c010e07060813110d11012c090a09120c110109 66
    0xd00c6100c01d1500717040300d240c801c82881d20901c2c0310000b0000e0344031030968403c91040c002400e41030703220344880c00314110000424540543c400300c1400000ca070f080e820320400511500c155005554103443c1890b80c0c00f40c8004440e8100580c001000b040300c1945c1000d113411615040b0406400a581580d942c0ea0401c80b039450043c01c0c11209136068000c020b80c10702e901a103402810b03040b003020343c2e540b41d25917000b181e941000ca0003180c0309540040f0510a00c004030301031003690341790140b800d070030204000003d410074254240c0d0046030000c00a0a400602d0041451988080140d0340e1641688030701425104210340745509940018400c00c80f261740700d03c000d9003100706001481d00180450500f120b61414426940c0c1d800480c3c080345004208041e42c1d003804e2150300f0307241c030206200d11506c01c51040c8081035041280505810301c0168910300007050301c0c0e00006000000038110810386855140c05281c819000c00320b4000c3e14140b0074403003400d41c50705812000340b8002160f1401d08820096116580b41ca = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 457409100 1250 457407850 457407857
    0x31209081b0604091d1614270402010201230612060103030c030302210712150605180d06091a0c16021003060b0d0f1a06160602040506040e010303030e0d0f 68
    0x16006900c145c11100f484070507100845000042a110000d02d4103114031030b4002c02030b0301c043d10404500b0819901d803004210005441210500030b24a00800d441c020412811556205090b810032403481c190740d9899506001e81c40e50f00e180040c01d02045000711807d1070100e5000360010800698007110034146198145009070700e030f95006420001d008000e10707920701142900020400c642c8da000a88007402d800341d0790b041c8002039642e851640c3c020442c3c0185400100b0411102c482100c0042400182d410060102d00c403c501d81d0300e0701ca00711a2800c41c115030302a02003044a02809441030407035049441c240010385040561908078160006d00d6a00902440b1035518011000f4000e43c40940248030313581e000c0d641c80d0081c13040c18000305031106102d0142d52500340004d0040d2402450840d03001006031440f0710308a030306002d20f003050072060412641aa002c0101059507120440a0320082c0003180c240656035040d0301c1e016090f610220042d80382d50740482240c990a5501a0303074241c00510608 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 457410350 1250 457409100 457409111
    0x12708010e0609010b0627130207020f0a060f0f110609061e15151c0506130e0706140c070609060314040b062101020c1b03030c0703110406031209081b060409 69
    0x10040c201f901855404141c1c80708061188101a1035682c000300042482110000703103900d603060801015180303c0c05550001010800000945802102c1100c00f441c49401c0600522079121011850400120b503900d00c25009407082c80341c4407065000509201b4104044820340e0302d00147d008420245800f6020b02c50b101d500340f01042000a282146c440e031100303200c1a15809007080b03002c0050700042d00c40500038008201c4100014040b4815040241d43c21800380c00c000e89017040449204801241c219081c2070b040090303d80c000c9041000c40e0081599407980360181d8540a800f40c219002c1a10380401c51455200300800982d0039500310368440d80844504514000140070001e8000c10142e0b4000303298400550203192010000301e03519140c0c4031100d50768139100c01c8801c1c55242e02410400c0ca066910410061000a007140300003c2c60342e0002d400002e8090307607600c40240e000c0d2220324a001140e41c00c1b509005e0f00e4020300071303090441031203003010004410305404180c04d0700c103a2003403101440c1d441 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 457411600 1250 457410350 457410397
    0x5210f032706070c0c12020d14010b03070611060106080c0714030903010f09110a03030804030f020a08040b120a0204120206130b0c0601150c0b06012708010e0609010b06 74
    0x403031040103401c2000c0101c0b4210325100c4070142000030041c030309035800710f0108400105a140c4032005900c440d4003410000e4030746480e0b0303560195044140c0c00e80005548a58205100d600c08120000081015545440f000041c079402c140c00d04106800c501c1c00c0111207001c00a0341d8544408a4407242d80c044c0c40c100c0c401030382c07000381400c50040c5610b05615509006545a115045420006240c1e00569140c02a080e4400030880c0341d142c140300003404600e03820300007804031b8020907409600c411240180c2c1c0100e03203213940d83e0065910070307000003c0a0b40040341800003004421106c992014000c101181f805e401c2043e080542c0505041c0280b00d56800a1807044c01a041c1090500400302042d02685848404150548501090241340c0da03401107540b61140c020300c40c0f150100080e40000501c820b80d1244401120800e07030104072041450026082d42d04e0880b00004071034010042e10000042d901c0c0d4a1203032504050b17010b40780810581c1841513104483c2c0c5c89030203d403802c125100881c0001c2000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 457412850 1250 457411600 457411651
    0x506071d0d0b071e050c011b02070b0c010e150a0b121207080d020309010606111f0207060b0310150614220909060c260117010f0905210f03 61
    0x84c106811048424040786403040d40200241410103103003002401054a0184d1130311007440b000c402d140059000a004200c014522001031205054540002c540d03603019021182c034002c020718180c00011816002c009016102e403040114451049480910300e900f0800308696405503420b07110394500d00020700e40c3c204131b0700d6412150288003051007591280340420003140202194401d141c04140c0710101a00009004200c0348000343d10352100e581121210910705000390440c4104940b4a603880e04d43d46400ea0703080124041034184140081035040007140c0820100e8072a600c0a4240203102c0300c41e072602300300070042d640c0c0410f810f900f1344080764201e103603105041d0a0f9449110524508107802e003d101e60703a00002140c0000d80c07590401c60f0f1109079800c1c014010320300c11110302c101d208014042103000d182010703110711506002040d40c10409074407074200c1c0c9a0301c40498207503014030410f5180e060245075540c800348181000c2c604101500b0440d003540c0c40300a08951f5280c0f4a61500307001d40d1403 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 457414100 1250 457412850 457412867
    0x101d0c0c070512070305151303120603020d060506040b040e0a06180f05031224010804050c06040f140616140703080a02030d051f061b0503070506071d0d0b07 69
    0x30024000500383ca801040700303850302c1240c0010b8446006200c18a1043d070418030005029012100381c1c020410351585003114100c20320082d18410356100c0600201580c2c03054011894213001d64400030b4503080040801080382d0a18010500a034203001310141100c40200c6c48500b1b03581c115801058110401044100307030458440c2c002c1c02c02d64080c101c0c43c24410000090224811900a902003940703030040b10100c10414540c800d140d40582d09801903482d44501044da8005c0e110b0000c03900140708000028034642c0068121180c10256034004101300a5041c420504806054a019142c008000884540d40707440c0140a440d8078080340010340c001d1020001c5500446e08284001c3d198082488002e45030f87c818102100701c54101800700e00b0045d481044c82000200300341404854030310305501a41c00741c5151680702d11454102c00d207600032540c10700080810510031009024103240c401000741006c0c0d08484840100d110f00a24051952100d400f9a107819801454104050303075251012034a540 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 457415350 1250 457414100 457414109
    0x604050f0a050405040807030e01080c070318080601090903030506090c04030f0f050607122004090e030906120103122a0602071b060e04140f190204030b101d0c0c07 72
    0x24139040c100014413070058080e0030814801e9580d9540b10500740700448413400241d486c404903c3d420002400081d0040000139a440359041e09410040e61f175004050411801b40d0180c4034103034031006602d0800d60f061058035888030f4100e409a0003030074044200d22281c091303404001c2c6800d80d03111441c0e051100503012040e10f540e0000845030799140c5200000c0c43c81030300c1280802c0143c10004000d010320515400041410b0300da9911b5801d00c4c0ca803000480141c503401240103458041000102c1c0291640700080680707000c0c02c0800807565146140ca41401840740407013400300203440192038502d071444050312505808076003e40300e26010031300307011009200c0c4500081c84000020710041e5154003940c2c81c0000c4418585603108100102400e10090700c20000e8540446280d0342d00146404000d00212900305042500200c000307920240c202c0700320303407103504207542c000c5001c01003108502e00348110f04040d049095880f210a980483c03a101d0510001c0c00b100381d840710101d0f402808a00c10002c800082 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 457416600 1250 457415350 457415359
    0x60609130903120606020d0c0602031005060409020a020705060a020309010c0624060206162c120102090405010f030f030c021315030b160f210509030a02070f050604050f0a05 76
    0x8654940034014400b0201d034035071004d0600313400081c018000301c1c01003d200c2c01619002d2201c003280e500e03903000754402001b00502ca0040071000c91940c40e08800390000c0d04e181080142d4503901c10700c01903d01071141e4091407141004010221246a0100586080e1542070138a00010300903031501d50301406030b40340040342000c0f440e9840e41002c480a40d032007040710382031380a980c265103d564665a503000b82c0040d07038000c2151035002c0f007103000c0f4000026411050010041c0e4074032911b0701c0080d44c4403441c00f0740e1030041c5e9000b00d0070742d40502d050b1080d9030041c070340701c02c172100319610310341e1000000c0c501c2d8075024041c04014400d817002c1d5191040c041c0010700103e50b041040b5508031400d0001d040150005451a190650000d0000d000e01040e1509100701d64813601000c95117000c08545c40050180100f203e0004490965a070801078024140030340c03a40e1014544904180c20b00910b025410f504c0203001d050304ad00208101d48401e01260f013a14001c1e20074903c111035140100d04a0500742d40280d402 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 457417850 1250 457416600 457416611
    0x30f0905041a04051f051c0204050f09010c0e0a06030f090c060f03060b120402270f0411010309030f0e0301060b131802090109050607060f06030b06011106090606060913 74
    0x44001540c01d02e0a03000b0841d03081026403122404d60440307151480c3d0180003481c000000780600d00d00b14100c041000c2a542d8000d81e101c8040e40803c0a58105983d140540c50b903a2049c02043c6e00207029010b52042946044180c2d2412900024403101e12031281c00145a42c603103040c824200030b0b400201d20b01d504800c0d4040c42c165580001400c54508101c0c1000007450300c0d002003004401b240440e4480c3d80904007980b00c0742c8440d0204083e003030715010614aa40110740303041480e08101548030b07104010181c50181140360030b0500130030701c0c0d0039030a82c14100340c54072095500080d003007108040d01e0111450700040000b8580c1c08039004180303d4010021000001c91500d0081003c101f108098948282c40b0300d03075110481880000345d0151412090210f040700106208904100700a002d00502818010a111000741d0444040b5615600240e42d140035020800002c0d50b001001c0c0900a8031202c0200002d1800c42551a220b24003d4021403140000059410855031a0034070f496050403402802c004 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 457419100 1250 457417850 457417871
    0x1d0d020d02102a020f0d0804020a050f061201030f02040b180103060e0312040510060618030803060a09020d140601020c0120030f0a0804060c050304110f061908060307050306070c030f090504 83
    0x19a14217250416a4920555020014141c801d5045a005a070301070880000f190800040200e1861080000b40c1c0058041c01f090054121105200e8000c50140072394041d8900b480c01444140c5041541e100d0103410248120145a00705014880c11a41c020714000b4940c44900350050540c86409440c821000c8214140300c24002c0c082406000112140c01c00c11100765100070540c0e2041007100048c41c4490751100800106401030b00840c8d000000600c0c07000c2d410749a004810480c1c05c046d0440d010f480c0d403800025829580c440901d50043e009000511852a48000081c0941c40b104410001220710354400300c1a804c0c100103481c80750444003492502c03492114002000184121000d4840c10300745118294154043c608503801a42c001d6685400800702d0b038144480440d4240100390844000c100c1418070300300008203880c036a1501d684400c3c240c10600c0400d07280c200e46802892194001030107000705150041641d40086616007001c81c003400c0021016212401343d40d200c5034005080511000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 457420350 1250 457419100 457419103
    0x270309090114060304080d061205030711090603100b1801030b0907090221040309030203060c07020a080706050a14070515041b2706091d0d020d02102a02 67
    0x20504058800e4403450381d0700c804080014110000307080d0414800c00221300411265401802041e54880c00801d031a40c5d13031603000b03c501510350340c25250b5401c0803400500b0000b8540d81c0720342030442101e0440c51810464002500c4030340d209a8030458654501c24042103403030300300c078124072040716034800c20496039a400c01e04c07075190040f182c40e1181c0c0940100400d550f49076100b6a58108080d21002181c0c520084c55060808400790081e4140040c284001006030780030013117680f2071506400e0341500c2d204c0500c1400850882a0030452468005c00004e210060b8060180c0701c50307222034540111521405800c00300d0520030b000002e4514003070003030544e440414003e44c81d4015813140941450000042d0035812100e406070145028003004207061101c1400200741a02d041030000200154103940c50000310200d44034610151950301844c2e21240c010b0605110307600030105180060203000c0c02d002402511013103402c3ca59003001d0790395000314540045441d0866064103010510042c0d181071000040d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 457421600 1250 457420350 457420357
    0x30c060f031d010603030908060c09040b030a0204110904060603021c1e1103010612090c141801170c0117010b1c0c110c0d0201080406020a14270904020d0b2703 70
    0x25404986003070400101c0d40000031345c0c27510603001310700342c1810101c0910810000d015070343c40d80d642c10b10620b03007110b001d44d0380c603ca01e500054050740d08075035404041041c407003990050740c1b112043c18418484203850804880480101c0e100000740022040c3d404685418411211886811010325040014031050403030300045050719800d80f02e440c000181c8210000c00c1e60303034194000b08404c03001d4004002140010172405648040280340c0c042401c0301c0c00c201102a1026401049803c000401e1005104000d01074084103410a281c0040150031944a4041028040c481c20314100000602c0240304154101080d900c1c2000c09070a100001c58118010b001118150828000e03025210b03041c00c2902c0c151511400341c50703068481010395138454071090001d420612241003408281c55203840d08850881c002e240d80c1704000348018541040160300301d90070107100502c0380075400740c4c1c0502c800f60340c078076155916940e4010791900d002d94800c8020110285004940d6100c5034000d0300e0300c3c00640000c03025 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 457422850 1250 457421600 457421603
    0x115021f1410050f0d080c0312160c05120c100f0c08010512100504062a021515060901030f02030a091a011d0a0e1e0c0a030c060f031d010603 62
    0x10240c540c0391080c292000340001d2142c02d0b4001030409130000c6a040c0995031400b418011141c043c03c026010300d500d402c5603c241c8a020141092908100c20100000a921004100e615010b20007510984ea200c1c0d9803242d084100c01c141001203480c00d01c080c41000000d2f036030710030542e0a0003011000d85030600a1f100c0e07640b0080c00305200c070f03002140d5401d158000c20429000c0d80020a03016242e500c0604c028400904142c80b0b540d01c40d414280e4821207400701d48240300003454251070b8443c1140c402400d001c070040c4044180c102890a0190404070402c3c5821420f0084903125610017000c001a030040101070142c00071240040208090398040e5404505114001d0304003524400e0008541040f4403070902446d4141d0308400500e0b480c6409040009034420f542c0c0e44002010b50060211a00d00017489416106c0283c0c014010200c40c0024004030350759800c01c1d10b000e0034582c190b951320741d0b4098880c050441082a181011001144242c001d40516240f4880c15240507013101c40482c0a020503010 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 457424100 1250 457422850 457422881
    0x60b030a1b080a021b070312020d030905061503010e1c0908070b04092412120201050411100201060902040803090102061006170c1b010b011d090115021f 67
    0x1400c40621605240154103401c1599010501c0d9580c501d050001e40200d58142900740d02000f903168403060402661002d14050300c0c40811103407000780000d10700f156840e821002c040c24501d2410000743d000881642013800c0001014503030722102c01003401441003551840c00e07403144c0c49012a08029016208011285a075100290701d03494a640c2680e072005445060382134141008100b00c545041c0d4080140041025840c00380c40d00c81c40c58000301c500d41c40d0011010700b400070290804015800e1b900e05131007001070000b48110314294481c00c0c102022025200e001e18000b00390184040d20030b602443c05010640c0086407a1610342d21819600c0d0400200c3c14050b1003060007003206000b6552100048401c55511a45d01d9480c8030b11001e2003040c054010701d4046410f004450342d01c103030ac0c0130b240310005103a000010340751402000140158030010002504068000d492140b540340d4030091415909403401ca00c9041c013640201703e14191b00c030120303101481c40d42e03020038801180381d40103074407802b24521 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 457425350 1250 457424100 457424111
    0x22050f01060e03150c090102010b0303031005180610030b0105040f030b1e13121e0302120606030601021522031107050f0a09050601090f1203110a0201020d0c05030d060b030a 76
    0xc00381541c508403201d14072240c3e604d00340040c1c0c0c0803a282c0d00030b100d00b202c10301c008541103002c100440d2840d00142d807101600c0ba031240b4184845c0c18003201c1851013018051052410342000008a1000500b810840081607200c004200340c0d640103108860041c010145024502e03542c90a080d4140402a41c80941c1c1c007010880780303100500c0d20510139020303020444151681c4a01603446614000442802c03005201201c5094102005030b540e500074010b0311628003583c0e9040503310350002800c010404d61060b1018014072681c2e984c0020705200c9801001c0545100c1c0d12046110960000560219120704032882d1000041542c4801086222411501240c07009a254001c01450360008002d0580201401c80104282402ea4101c0c540222041c1819080f05440d68891014008181c004e400154404c11250080545c4910303140ca01050410280c0307144405680000c1d00e501906d4100f0301008a800741c03281c24003100f4012039142c500b01410030006d03141d841c1e4000a0b07540040340d1001c8003602d0a13 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 457426600 1250 457425350 457425377
    0xa0c030b0406050f011b06020313030f02070b0901180509070203070515130320120c0708240702030c0607020c01030b010507050706110a0c120501050606040b0922050f0106 75
    0xe0003280b00795003004007101d0340194040f004642d9400b8000000140d02001c0b4090004501640700950150001c05400000d2000f1414098480304241c0c0e9001c1c11580409030030401c020707503002550035421702440e0403800c0f020340c0030f189800039140b074110551158170380782480700d1650000700a0a240d0321801c10343c0d0b03d99042c101414010034040303400c0074840c00d07007600700e4000a00c034500c0041c0f00c5240e400780c840ba600101c0c01301f0345881404948000e055000280110703603020104145802054002c0c0289041e104154100e00103d44c641000c505000798000814a8940284203485141d880705084420500e0651802550303081c01100c264046842c18140f100154898011038204541200040900350710b4042c00b01c1e80c1355527941c0c0c42c244500982420000089680090303170003c08645441a200c030505040c5682119405401c46103d440c0400041180540c2d400551b03004070002c540c00d80e0918002101000d0000000f540d229029103008200480403a00e11881d03810780c0d400da0784040740407444 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 457427850 1250 457426600 457426609
    0x21207090f080c01030207330f022503030204030b0a02092403040b0709080d021b0307030f08090a122009090c040513050625050414010302030703090b0a0c030b 70
    0x180940d807455041160505044e50207031300103002842c891010b0760171a0ba003260065521540e071009516507209410031800c045180d0380038100210b05184011894030031000041c1c0c0f0311000020200d9000340f8920f00389070925000c0e80c1a60000d64000c69580d4040c42c026480800071750040401d02e201d13400d0030020900c050210703080e40c914600030040c61071560b1035941301c81c9042d1100820381000c01c050202c0210307600070244003d40c20f50b0003d400a0508613032030a03c3c41d0003c098030086901035881294200f022404070304055103a950005181d56803054410082420347e0007541200003110000320058003000444003280300c0705131100544500b0011140200404040d00355a4100c00d07600021008400d0b14055005d0b80e0403000d800d1552000001d43d56880e0f0600008031451040d03d000a40241031481207030811410304145490168605400c00c0b64410740400750303a800c14100b50740800003075010342c000c0c0d01041407150042300400d024038108036a000038118160003240064180354960020b03040 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 457429100 1250 457427850 457427879
    0xe03070b19090f050f0d1506140307120c0b070302010e01020f0a0210060e060f04020910170919080927010918020603042a060903140a05060105100302070602120709 72
    0x1300030034195848000404008001d020a079080e22134820b48100c5014044652180c00003c00890410301c00f41c40e1b0b56801c050800303181d54045041002c00b140800e000070040c0d0b20316020781d054809995119002400e00324014083c20b01c0c2e006035907100007245040c950100d806401000b10301d608031084c4091390b41901080e40c604d0b10504509081e2000070a10a15218142d04200040a00300604043c6108009054480c090303030320030302107980840c90000780012203845940c40881c440c001d000762160074022452107007a03080d0181c00b604c0080b49030101c85e651a4001440340205400481014010758011000000d00f849990f0880b40b41c03c41010790000e0340350913001c2058000b8005030039a540c41d01c9100e0303130042d0101b22844056101d02041d1041c00c0360811000034050640e0341000e014158030340250105102004501240c1c09075500100003240050100c3c10344509070384261000d00b01150560203801415001800d050012641d000c0740c007880c041d41c40c411a1113070740d070b0b80c01a81c0d41c0050100508 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 457430350 1250 457429100 457429109
    0x6061b1212070e09240a09061a040608070c0204060302060c0f0c0109030302070314010618091205070809040e0705030703051c1707050304030504050904050d1e0e010e03070b19090f 79
    0x10340f44c0c800034441984101391140c0036004103000841588440c00046c0018500742c0004503e20ba0b00c88051000b5000c0100701001098034000c2d05152505002000c0c2507901d00403d40c2c0200116401940219101da400c408000e6502030f14140d280c0700303c00003040d115400c0c962000001d1003a890700300c800350301c43c04c081000c480e010b030090300c160342c01c6444004d0580c14010440959648030200040c0c031020008040340745644944000500301074905d01001070000e200e1141e4208501408540f011580e028126200b48408031000280e010b054407001c1c5c10072026a12440e410b000e4103e00105001010039506500701d04440e811040101c40310307060392660440c101c0000181c841800180310f03036011380003d6810038042c0c02d08509140d035070400034009200440c3d0885041e00015190b082031a009503161840c0c10a010b80415100c841440c0100421680c25041e070401000310b030900345584052003408090103105100594858008006a42d044822044007001410b9078900041010070100d00200380c3c0c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 457431600 1250 457430350 457430359
    0xb03010c030c0504090e070e09330105040504020a1701061410020307080f071b1508010e2d01140a09060b090607060213030516090b0906061b1212070e 66
    0x190034906000006d24a844460394580718840002c290b440e100701140e80b041418000030103441101c0c0c0201d01644101c4090f107015035030440301e44440c24070803008850640f9820ba0f00042c0d16540d500000e0b111900c1d5901c400d01c40302848003c01e6a661064200d02d040e122501d0f0303040119510401804903440500d8103450050700180014800558514000c2460203000d8402d142404050344900c030030b81400242507c628201c0c0d800800c0072217100c903100c00480c61541411140e940c9001d5807ca40d084004181c01c0c00c10301d0549007010598280d0034521b520210300100764529603101c2014910095030070601d00c0c420210000000703040c001e540600c60580d04c031400301c0d50505081900340000e9400031803040302e40c1602031000040603003082004c1030085005034020002e1007a41300000d00150b50b15040000041c1c1004241501502c866145981102d41652216610444660303140702c40c4210025409050245400c01650002004060200c5483e03000c0040450b86a80c0400d40b195008000510b421 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 457432850 1250 457431600 457431607
    0x2301140d080733150503030315010509010306320613090507050c011b03050108030403171815030603120c0606090c0409140a1a01080f06030703150b03010c030c05 71
    0x42107000300302c000344100080c41c0c407080d8800520043c0d20030120002d07031010381d86a101420551864036224000c00068020b0351560a10450700102c0d4140e104081e814400d0000b086001644264042001081c0c0c035403c42843c441c8076006d803101c0420004524003078800740180c9040c5e5150000444a20304a41c140e6403440300d00d0880403c024000083c46841030050070f03c5903403a100028000e03094540e940905111100b10f140c500130301241c4060b0400c0017a50b10600023400081e420f9280d02c14441105528241c50b400601c40b0100e0f026010f490310364000460100303001000310314001450141e44100d041c3c0e40030300b290080300c01c02d6005500900f1020b612140c007050706800c0015070290000e07800000c00d0300d010749412020f81503555074001a4400880e00c801c1042c1c0309401e01c0303003185042c220b001100d9042d01c50780009082c81c001414036007880e50a180400c03031a5904002c0e9070300950384829644014035030240c0d110b00428070301101501950070320700b894201da4481e10424445402c00d0b2100c608 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 457434100 1250 457432850 457432853
    0x19170f04051203070804020406080d050d02180a0f0303030b1f1b021207031a0906071b0f060c18181805010e0f120a0906050a032301140d0807 62
    0x415000d801a0740500070b40142c002c0d4514203800951243e407042d11513840c0c904141c8103100c00c4a103d5808020107800601855280652000890340703c056954005603ca034030081000d2203002c880c1c44c2d680d41c401c1d00c2020018804800c1c1c80c2c40780c112402510108442c524003c1800903201d100540345c00600200c0350030100050141140760f40c60542d0100a03039000c002d550109420491046081003250b108010400402802e8000005241101103407076a10382011012240d403100c001c0e140d6400c0c031018222501262201044100c005508028400030841c07440c10032034000c0c0305d4101943d001416100360540c910340c9500c0402d048985559103d4450a01d04c01d200e0001d00200446640d6100c030a12800040f58003402a084003203038450283c0006c0321500d0001e45032040000400309808024401d58440a401040c2142142c026040031507a4114040044004040e05614400082c24962080f2401d034110b0000d64140d400c481c038030a806004100400416955540b0010701e1341e0410001c190 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 457435350 1250 457434100 457434121
    0x20607050a050909040f021201050912070b060919060915080109020d020f040b03062d010305190c08100509190506010302060d150605030702010b010906020309041e02040b1917 77
    0x1980a0b0017800781d0106e5142d2a4001040448a50003020a82e0344420602520b50003d22021040c4039444d00000e160640e266201c100b4404010401e40c03080b0300c0c0074005008080d0291105074002c100e9441044890303181d003440c4000f040300e80e40709031348a5001c41740414031031014806c210080380c0040900031500b03296400c00c000f00d100d081c05160010f80700d020b09055900c0c100086401007050038040300d4680315450071551614040d503803201c460014030004101150001c107000604120701400000c0134081c50074515143e01080d840642c851280d031410842d9103403181e11160003100113400341da0846140084240d4060b195071000b800d075401c00001040180f4011009105443c1015070120304181c14010340080d00f003040e13004002080300042080b288a90a110301031210700c090034845092130a00320025a41e0241e0b4074038030300a0355100402c005406080446000c00000388105641d22911b900b503070106c5410420141103451076005501c48181e004024500c0d011a60108c2e03c0c20760b60b120240c56 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 457436600 1250 457435350 457435369
    0x7090503060f07032408060604051003030f0c020d060e060c031005010e181608130f030f030902120307060608010204120201050a14120f24010c03021606030c020607050a0509 76
    0x140241941c81c40381500381c0314020503507441603400041c0c0c5c40350f0350b113011492424040020041440740f49814200101005000a0001507030b406180803004070b40e401d10147e9224110a6002c1d41c001d0000386040100410340e00002e01d55118101590b030982c886542072410780c00140d58400c0031446244062016501c902400d82c81030700c000345941e4200054448910005205032540c40e1401e455540700740d42c07036030031a648a070018040a548010740c03640d074440001d01094045d0003030800003907103100501c03a0b2082e0450407900d078005007004803461241e00e081d552075104c0c41d01117921604040000030001410310a4508580500010003c1c241c6c05500465451f40f0130500744090040e88210141c0c242d0001d0082c0540b0503a030028891541000d5102c0800040002d013038030030f14114001226880040229180c0b0f24030020308240b40c4007002490b00780d08203000804a4041000d555400265166050b00321080c24507642c3c0a588040c0c695540c1140c092060000020111301e00704204a031b117003480d4000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 457437850 1250 457436600 457436611
    0x40b221511070c0e06030d0c03081314010c051e04080a11030f0f03031b0c0705061e0d090606060c03050405011808030c0c09070201020403020906040e01020702060703050406030507090503060f 84
    0x2214980701c82503441c1090880707940c10410550034294100300e11741c182004020b460781102d0030015406802c61707800500c8464014004183e8000040740703481009101910302018180c0400280080003004400405036007008046400c0b41e90300a0302c030380a40070220111803d560718600a80b0340500c03142c0305c1003181c0c010b42d000d641c0c140c880d8041501d0320120602c100901e08885802465172824040725602d45604036090403213403503c081041c0040b080c00000c041040368800d0f01d00079144c400d031004141d2010210b07849801c00e4400040e010726444441e92200e080c0314400c540800c5010b4560b001210911284c400c01004038404000c01c0c00f0382d41c01861760102b0030115004200016465200c8241960058012f8148503800b41207426041d00d03100100d10b0384040188021802c1914540018a0810300507044500895490340c2d0040c08003020740494000315000f4011079960265450001c216038000c0c412100003e141002141d00c842c8582001c02c11a1402802086d6070340325800c11441c0058081c00 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 457439100 1250 457437850 457437881
    0x11803020609061605010608100509030a03110f0c01050105091b0a050c011803050a02100b030307140a050607050301030b100b032202090a0f0e0a03050403030c0614040b2215 76
    0x806000b0758110140c00c01130310310031307400450f005242520207444c0400507003840490324106010044820030003c1900c0745100c451a02280045900b1407030b4500f4070982ea0804116500014a09018801504198100c0d441030f2107401c413656518016000501f01da8640e030101450400c41a02c695200b100940b88589811000180c048108070400007003400f80141240400c00c0031402d1040c031501441810008240507200382f2040c003041c40002d4403440341c0e440c002c10155890703080c50340603642040f140700c00361307409030448a0508141501500c80d4100340300c2101c01f010368000107a414007510f0030384400c4915249445040d602c0d014101c880c034040c1d5205665140000c410100c0141c0c2d114070009000c1d860341000003034101c0e44083c800c0c0c10750b82100800c00c001d604c0185844001b941c42012641145d4052504024440302454200042c2c5001142100c00150301000e20050000305048140100442c40c80c0c0e0490034807800641050454500f0702400c42200d074000c06400d8a03940d040448461134549 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 457440350 1250 457439100 457439107
    0x2090f0c0f0403060608100509070605070302010e190c060e01020606010305040204020c07060e03101a1203040f0f062c0402160f0614090312010311010c06020703030b03060601180302060906 83
    0x1241c501541180d8000e6541c0c503100c0c00100b08159092240c1d4003c042610014031086c0b8015003c180d0b034100d04e11600c402c001000501d00d06040c401c0d800305004145d44c0702961882c0303404c282c0400081280d02c4060758400814080010001e02813403866035054010b070050320295540b40019001044000d01c141d030030a8081003202440d00302800a1005440103458007100089003505140c41c1040c0fa50020710032510303000c00c16840c440f100741c0001c03c249045070000c105040310281d103403c50083e580061103507180302c04003259800c45061070780c0688030700c0e0341c3e01c0361120b003002d0f05040d581164040710744c0c0e61041038181c5000c1d42060f40040524145205807060300d00301a64424045031600071043c0c504d55902d40ca803010ba00040345a00e604400c00b40002d5042c10a008055814500c06210041c940b031826001600564010050f104225800040444d251041c0e4240030300980500344141d4413074010b10b00010350a41c050310442e200702c0c244c4a190412542540d0901140e5842603a00d654481c1082c07 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 457441600 1250 457440350 457440367
    0x90503030a140903092206030f0b04051c081609080a080405040609020901052d03270f0703060906020706110d0c020303040b04030f0c021005090a1202090f0c 69
    0x100029401086540780002e0030501c804a004000600038001042c1d0341c004011501c102d9503010007840a4214205a075043c070f030b4110305030f90300801065000814001428442900340200310958a100f14014401c1c0c0d020360100342c03004407049150040800105241c140800e81d07100341035283c1001803003a0306000d25001d84442c200351031310003841c1d01110381c1c560016003808141094090240144003401003581000c1140340040e015000b04040d082d0150b40c03070441d01540c42005082003500714002041c1c0c5960f420150506141401c11502e50000c0c40180300410b030305560001641e5484400c44005041f090303066545000c0900040307002036408940a11100020076010320401000c450000c41c07856445100910000982d82c01055800540d0010700400010940501005502c103916240c01065442c1000064030201e00340400a034121400002020170a42c01c40014505544101d50500240380d60700d859800c07000d00e400000b9000100600800c0782e00401c4c02a03542c10854040c515400c14103076 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 457442850 1250 457441600 457441603
    0x90109030b1911090f03010515010516020d12020c0909070b070c17030903191502210f070921030f02030403060c0518040b0a0e1503010218120703120509040905 70
    0xc2590500990b80c0018601c40d503241445c0b2418001380d040c1d0081c422480d0002d58140040c0c1200283c6040c0300000600001c26541e810440c107115900a00a1605c0640d50402c02100c020044d80704c4050b00c10540360840701c0c903040150072f00c6407405900a0a0f2241044818000354000c600112003549a072203010880c00c1c0454501c0c0404101c010095032981c502000b0945444a50000b01907411007080e43c1c007011580c0206600305040701c0d06405680d071030507035446407401018000c0d1113031124045070a0200400441c0d0341c59014982a980c1c0c042460740307480c034282e60101400804904400b000b000000040c0c0204003a4006015900540f0b0500d80d03291038440130340c1d070814011000550300140380242c843c200822074000220543c0e082206400d45400326454601c203024512515400b000090800d081d14103070301c0b90200d00540203540f110001c00600c07100340001c003511352081e840c0802040c540b010005000f0216504a103180c0f9110310710410564065009403521600b19440c2c42980d400f00d0350 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 457444100 1250 457442850 457442861
    0xe0c0f04020412080a0f050310060f050d1d010c2a0320060910110d0b0a0f1409070206061e060405060c1c180e1509010602100f02090109030b19 63
    0x1460156a10700c05044010200c3c01460703001b0040c41400d00620030301e030040c0d8001c2c4058424030300b44642c07103801c96101501c0178003070f40c48006c5103c1c0c201480404084c071401520800c0d00e400e20000e100c0707842c0046d0f0580d60850381041c0b20110340000341c4000c003044000a031518440c0d010b414000c5c6e80120a0031030441c88090400708401907031009090000d420020072000466146000081040b0181c075000a002403044104400f220394031608890502c0e80e80d4a0000010f004242c2c009603510740e2082c4100040f200221118030540780b803000920403a0021034814032841d0001c0a14a100500b81e8840b211912040340c16500442c3c00e00000c02d00740ca07820001c02049400f403004015507004403e1600002c03851460400030018200c1803a2100700014504605903805100301001556494103100c008078001c0d85110f50214040000098154000c80c6640c081d046030902806038050f03107100441648240d00c08a80020603410040012807002ca142c01e80100c9003407034401440e40380c0d03080c050aa50 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 457445350 1250 457444100 457444103
    0x1503150b040806071115040807051c020a0606050a0308120417030f061c0201090b0a02120f09180603150c0702040f0506011b0b07032f120603010e0c0f04020412 70
    0x107204005004441e45c000b40c540800650000080c40100071030031503655010740241009100c0a0003013101c2082000c01c3c032001c0181002d0303080c1c6218040d00048003c0d60750000d40b5064410519003000860203081144103401070b40c0e0030120840c504500c115100d00c01e110010701c1a52a15001e170300e100502124003004502406054a41205508000c402c02084888038a41e031100075511b40100c000603600840354000701c4410a51441c0c031018100c8081e070400c01c4d0310390340664414000410b500c00d05000400f0340004007050302c500c110030402c810f01c1001e149041c1e6466134142e004010120401d424021410b40c416034203409941000c240ba8041000d0324035002d5640c00c5651100b04008032540d1002105807002c280c8034007400254040d88038603183c1080034040404054460103081c0715959491305285594804175006003400340c0100e40c522080d040202451401207100700441c1d030525050081c40c005500307041c0586001c0c4d00700000c0005a004403101da40d00a40c003488001a1001d01260810205 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 457446600 1250 457445350 457445353
    0x60703020304020a1d0a0f0905101d0601080c100e1201050108010f0c1b050a140102120601090b0909060a0f08070302090906010f15090b0c1011041503150b0408 70
    0xd0070b0a104018480b80a504407001d0180c4c58848503502e040e0b540d2049400c03050083c03001445940425003034000e480300c0240a4a40c0c403580d000d6001c0d844041d800546050503292241c02c1c0c0303003d07140840341c0b01c60b020306c6491120351042d007000315686440c000740c410000450804501c02c03140007005c0317101140b119a00101595494004202264081c02210050503100408201c403810001c00541005c4c3c1c00e20f00521000c09248030442084000c0110146003504140c041c1100e420140ca4903020390710482d200b5004600e039001140983d40220342c080143c8441c0724140341404950b074140042c01034014503455004880200c00074206041801c1140035154a02c050f0911a065005004c00c880028082c01a00c0e403040d401000403250405404c000d0707421152200b90b8001c950030b0200c458a440e600102c01d20074001401607140000080d1031801e0185c070a1080c8405460b0800c000c009000718403034282450303068502c03009818032960240c1e040800800c00e02c0c103215110200c4103c16000b40c1c000b07001f01d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 457447850 1250 457446600 457446607
    0x1f03080d0f0513030810272004081207120806030c040c050901090b1207050304030c1a04140105040803010b0c0f0304030606050112050c04051027090c091a0a1106070302 74
    0x38154441045c650100d18100708000840ca0000c039a01d40b88115030300c0106449544022040e01c80b0650002110b80c110b5104160905003203240003182c2c0c1d070091003083c0f0341e84104129102003203000c3c0701f6101020303042001402c00303090002c411303521150700501299250003070344101d15641e0780b1b83c801c0c4480c0c080d01e66103494680000320700242c080700c4240c1000d01c1c0240d00380301c5400c10340c000c8010640d20550900d002e9480351601e103010b4500b6610788000a00032030003000c82d4404407070124180c91040b0f01030301d02e10032031030900350f421402c888081e80c005c0c12440041005100712420300006000d03103000b0700100c0d400c68002c0c0032605e0445d0410b0308100e40c101c0c1c98040070001036a00618170154000449420032980c02c00d1000f003d06442988034480c06080e0301ca241104060040114801048003c3e50380440381510002c4200c440d040f901640314081d1600c13103a81801803140b500e440603103000380b81d80510305035403030008034042c0c0050b10f68a00700220f41101c0c0c200d68200b4842e460045041d601e01580703 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 457449100 1250 457447850 457447853
    0xd05010e06070815041503031b2009070507020a21170307020c010f020c15040306150303030c02070e010b0304080c0d08071706010e0d0503130308121f03080d0f0513 72
    0x2000c4000b078130034074815070030901142c001c0d500c401090001c03698503080111240c0109003103161901c00e0307000050300221550f03003000e112180c0c02002580e0140c0803200c070b00f001c2d5150442999140101c0030041e41007880c07408203011030b01d240c03115106400700b0021100b000394850395489502c000c03a02141c0000c0c1030088184003c2c2a0103300b942e510141c00d080002da0310b080f110b402541c134441c144865124100f42d0400c03410121140040302c000d940c0081007880340248034411104045c010b840110000b9250036550095248041080d0b0151500810305890340e074680214141c05403c06841600d0302c60302003100300341801c0d00b0484c902c203000c5541c5600740c5502d08444081c12078a008280d01681c00c00103000c114081e0307030261030700c00d1080701103071040e231215803030b0500d40e156018a43c11a10f80c0113038940c020040c4100705000d000080003554050543c0c0d5281185034101d1b8007a0f030444205907a402d01c041c4009003100300506035413070b48840c001a030451150304500c00c0d260103450000700585508400300 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 457450350 1250 457449100 457449121
    0x12020a11010e070302010c12140d020c070e0c0f0c0c181006021609050702100f2405030304031e06060f03140c150f0c0102040b0405190b07020d05010e060708 69
    0x41c02d0100d100030704030091641c0c0018201c9039100c84010013462004000400682c025815452600da95106150b01e0700c010341c80102c000d5100b54403841940c8141e10000580d1840c14125a1144504000850801428485a12280d0800421380c0418080c40318900d40f03581304c02c8201d00007018004441c0c5d14604140c86542d24101aa40299045401109440c4c030201c0c0044800d10480d03104480c0016070fa516040c0882c1451072400d00707101554140000c103110407015400c1064008811907501802a400c1ea003008400c550fa88110340d01504280000c0002c1042003011602c594100001c80360001200d41d54101141d180d40c0040c91007044c1d41c01c0c240140003201c1101d16840ca581c4000303050701010000019001000801d040c1c514400008140da14080347c44103868143e040c8078000d5440300e4440034024660780103030142900070785004403100130707651000c0e40741c50450750500005803900800e50248051100010401d4400c2d40d210405426030b944204440c034411207517551501c00c242025580702 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 457451600 1250 457450350 457450361
    0x100f09061a130b010527040f020309070902120708060604150c110301051e0621010f0b0102030f04060e0402071a10060309020f040c0e0307030804031205070f0609020112020a1101 78
    0x7405803d1800010400d42d0345c01c04112845140c00076101e44417644072039250182040c003070440603003207030510390101d1800762960082d602a00c0820141c42503aa00d031202d49007280500d0400064440c822400305a025008810143d04030b00d000e08464502629205090f26441c100e44c1f41c800003449960a0505000a14541e4500c50034218028041801c001704400c201c2d20780e810003403c00959800103c1c3c0b096a81048048800c41110074418a40c501c60680c1802004c03a0302d18450b507a8104014104903610201c211090321404903001030400f420803804440103491404496045a0300704440000304582040c1700300210701b2a500344402d0701c2c000202461038002c1c2e0380004181410800301302c006943c0c00c0b500010b00030017601c2c00a04080c0c4000300726200140c40d19000d816001d041408401d00c40307413030001d2040c0d038020b298050030030290003003c450501c00d14401515103010161084006415504000c2d081070051511800241e201803006017282c2c0700b20480d00c00f02d0080c203445c0e5108103003170080 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 457452850 1250 457451600 457451629
    0x1a0702030606041a09090f0123010b04030c060c0201021002032a030c0a0c11090106020a1403041a18041e060503060c223507030302100f09061a 63
    0x2400300792641c0780520036400300d000580d0705c55140b480001c2d201040410901254030110b000030320000c9413020384a0050500c0d502c41100701d0010381c0c0007042c801c2c6481e0488003201da2001c5540003603490714a04440540c0c03c9070040f8114090440701062501707081c000740d405a540c60240e460303080310f1401003040401c070200f152880e0810500c01c10000381d201c5425181c94940e2801e02c0c03402003800745040313000156501c1155600c006000c0011407076907400501100910710910104204440c901c4000355680603501c2001881c900034031081c450303540c0780f901826400b525949030044051003140024140c032030810720345840d0200c2000c41c0140800394058400100300c168050886401c1100c5440f884d4401d90851540201c1000303a803448020105070900000e201d14159000e110130400104411232240300b5441a8400c1c6107903c1509140c00811000d041300c2d407540060524149941d0b041c0c000e0b001080b48102403030303075603145840415028020141e0b10070201d0340003030030040d6003801c002a10024450 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 457454100 1250 457452850 457452859
    0x61506080907030c060e0109080307030806100801140f010203120a0b04200a0809030d060308030f01230919060f0306230604020304022b0507051c08030604061a0702030606 75
    0x341000440c544e0b041a2003610300d0fa00e040c0a20140c0300c03005941c1d80e8055032104289200006540050692180c511405840c041b94940d4285080c500221a108020700031000b0114020902c1612840c12905e911032030141801642d08101c2260f1500011150444484203401c0d2908000c1142d482e003403103440e005018100d801a1244690901c82080b030150340306000601107800042003d152040099a05a1843d60f08c06c1c0300f00740c0c50b8a000c00041d0070a48950340440b11460011840950450f072010b112100701540c2150f8100c130504200b10218050301c02404601c08080c41446400700340114409806c0c2e02d400000b0561031450801c4c115100300c0c48404280a40210803601d040b030070001c881c0c1201003250090b86989403030002840c40c6501098101800c406010089013070103000f16404a20350042c0c013900c007005e0740e500c10721460180411307180f5030b50340f8501c0748180000d02c40f1014580140d0041c100095035510b86400a401d05038480188124a0300070680d9800c40c0790030866140e00907400d86 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 457455350 1250 457454100 457454113
    0x5090411031e0f0d050d02090a080f0102070309052209060b102c030d11010b04180606081b040e21120108031c18020604120b060d02010f0f09030615060809 68
    0x4014094043d04141b8610b242d00099405c80c10b9903441c0d100b0019140c42c00039134140c1003030305034614001d51000b80d080380400c4001c00000303030914140701c400c445018401d86090b0101c4900317211900400b00800c007112800d546160f0502c190700d440300c210040181c035443d5008010f0103c02c900c3d140307104c002c800040c0c20501120040241d1804604204851940e0600c0000425a0300665014245458901c1d400c50b00c0c0041d81d040100781c46502075003450040d80704100c51500d42100e103448010413100e04144000c0b500040e003160400703a004440240a590584140c86590000b6114885628425a00b07000020a600032129141000d55004040050046127803000c103c0304c06000010385030307611848070786c0e4880d03415112403140c000c0c15595900801490b551510303004082036074080360500b504c10f901d10600003038880c00c240f207400e000d81d5016100c2d03940c1c3c0d0120800807a00e84082c840850204048a070700000020324a020300003400485d81c0c09a1901c5051420041407107030002c010200503071001d03 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 457456600 1250 457455350 457455373
    0xe030f010204080d0f05190f0f02010c051b0a02040203042d02030a030c21120c02010510030209180a050309040c050310030b0c07150c14040b0405090411031e0f 70
    0x44010300304e8000e0902405080042e2000c4d141d41c0203410811075140001510452a1b95128117111044001900d85180b00b61011134120308960340c95400e840852410420021400a83c4c0301100002c3c0c25441190201c00c816170115050b43c00c141c4080f1030307071400c0e4000051541c456401c44000010500850000c6c0c00280d0006540c4900c0080042c09200c2d44041017410320020161804041c010325076098044031001c0c000510f106042c111075500300c0d1900c6010540c42c0c0c4180a224015401da4000742c030241e086800300701c0300c00c04c060002840c0002d83c0f0032030304646906105155250b0b0007580611b840c0c85d8004103010030344081883d42000c00604008018171080c0346c80e841d005981d00203407034990560724243d11440602c0740e000c01034143c80d42d40e49411102d002640103070440e200959035083c0445040c01f5004a071740180c1c00341c542480310902040c4980e040054800f0750040c000d080e52600034112901007410550b00c200e00c3c403000c0410f2a8090b0541100300701000745681244010700094108 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 457457850 1250 457456600 457456603
    0xe060f331c05060409050a032d021b0303040503060403050409060e070c030305061c0c0305010b04060f0b1e07050c010207060f05040302011107090e0303010e0603010630080a0e030f01020408 83
    0x1030091062246942d50302061603a111a40b0050050380d03c04215140052281800752100000c80c500c5c0030111007a882c0745c4005000004400090613968000304100081e00031002c9440c4600c0c0d4549805210601000505071707410001240568001e4a803165524104000c0c030055544941004030006424801d110003075502c0a00b0541d040d8162038000349545134a00002c40c440c00c1c50324000d1808441341d04072414090b040c0c00303001c2140d100c1e100070001001c01e6410300041d00d1952043c0303403007110040400c20410700c1440003048091210b100300410310420031092015600924002d8500e40e21420140e45c507541c04028a801401712828103001d0242c02100081040c070407400020304020114000500000003049150080d000450040c0308500052a0a076035941091041401c0501d454010424506041c8a00700544114005000c509c1c8a600b1418140e80150142000490081d40d9104046a41d01000e4031103100030795244560b20701c10b8030405260440b0001045030700c1c1d20402040044950 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 457459100 1250 457457850 457457887
    0x501060f0309060902040c020d0207050d050c210106030606141509040e010b1008040c0b03010807090506011112210f060409020612040309030c17070e060f33 69
    0x5041c540810203950601c1c0c98006001850f0000303410506001140070245d070042848114001e455007210840e540d04c01c00c203c3c00d00020300d030203405a00072541140e02405c00d125156042c2080403411044042c84c0003100382103500359802601c00729510b810a004200c04140040040c06046035810034034201802280410305c501c403140d0b442240d0f20483c1c1d00040b403081d040342070301e500c0050411035508030700000501940012241140d880d0810030002c242c0e1541e40055034107894028005140030350030060354800404024040c14144805500d61020001c8200701c40c00c12540c100900030344500c0214880301540d19000c20851403030003810200020007180c40b8510368004011180815041120f001083c0c8074450303c070b010014078a032241040305058111281401b10380c403650301071072160341c0caa070b56010481c90a02e0b40d8000d0b80041c2d80c01c014501102c0e20035a088400100030200a011400000340c45404140b086428425140d414040c0746100b61542d00c440300d20241c00f039180402641400a800c2c2 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 457460350 1250 457459100 457459127
    0xa0807030216020402040e04060516020a060f11070309080601060c0305090d020f0604090506030d0e0306160516050619091a07180305010209030f0304051804083a050106 74
    0x1603011444011250006441d0b00c15103030083c00442d84c894842002481300351003200d00362001c6042c040801c890f0103000d50b60100c1c00c0348503406019091000d0382d41002400c03500c98034444054442e1350400b01004914000e0694600c0303502d0b00300c14645800d0005040c404168031000c28050a13400e5400440d41040407100726110840e4407034100301c503610002e40072101440d62aa00030602040101d52003002d5440f03140907641c00c50072200100020b4a0454860900043c01c036016000000440c500440320004a042e0140d00d04005041189103a10f404440302041c0003030300c00764800380900c9680f0560740e006480300116500300b4041e114050b2185410046240e410000150704e420015003018800c800d0004a91403034006074840a0352818070034040d40043c6109886401144d14a00780020b0002c2101c080301d034040c115009070803a0b00c1607901da0550080c000d83d8007003020001d03281074044510008940745440b98000c03084032001c0007404004490700c6004018103103081d00501099030005507030300101 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 457461600 1250 457460350 457460357
    0x12c0c01111011040f120c12150b0307080610090b030607140325080406141b071401050112141b06070f0c060504090b04060e04020103021308060408030f0c0a0807 71
    0x341039580c00f00115226550089a040703035511404a426622044ca0390744483c0120201c4000c16202c0403240343e02030310700708000c0000100321a14001d001c1a80c000f03c1843d80000d05481c50260b60341c070b80c40e0805004032490300014180132018031a8101510a202c213001c0d056004043c24a401540078059689031001d5000d110404000120a030032043d00702c6c0c0c00d03844402c03200d401c150320005000d080140d0a40b0120f030034034242104444030060700d20003244a1640d10f0034014200d040104007800d00d500403402500c0e0141c401e681010420030900a00d40203003800c400142d580400c86c18503091f0102c0b20b4a10040340d401820b1369034a200c04000412030400412180f441e500d88840c68903181d011046117000704400c9200c94005000c03900100a00101c0d117070074009000e0840c2c284200400c07100280980f8141d00d09240c00f05015511a50103072034984800a220b203203840d1118541844e00310101c604480385000042000110525042045c0e0400c00b004452030a00c0c20411019000f900d0082140041 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 457462850 1250 457461600 457461611
    0xa17011b180e01053706050d060905060109152a020103060506120f180123100302010804080a0903080d020c0d030e2e020c0106032a06050c012c0c011110 67
    0x90405501170700e24001e129042d04c9144983e540400341441d0058511021601d151200000308550780b402842d2203200c5c160741c1c4030350560401401da624107108101c0300d42002540e01228104a50900900c002004440c05118421400d4400101528000d411042c064007040c0322041d151449030445903084910350048203000c2e5141c001001007030000c0c0040b50070a600f0300110034074514942441c501da003103003030310100078640d0f500c4901d210305421488000d001130442400030707001c030b1010000b03030111980c6490000021a036944855440b07130415169015196800a101c03035900d1420000352401141500b002c0c045e0031051500d03291111030101c40e44600c4001c1e24060410f565400c0714518a0070700d41a0115150314000841d103001745000c0c041104c03250070000d400c052000c20380e48a9250285410300b2240e0544c1405c10499042c0c020141c00800c1e0764940441d100070768160440003010081c5612481c0d440c48c40000702501e007103403141d440c40c10701203c0c00501c82a0a0045810000103080f880302051 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 457464100 1250 457462850 457462909
    0xb04021e09030c1f0f02160311060d020c0f0105010f03020907050306150c1506120c1002030c0604030518041b05091c0b100605090a17011b180e0105 65
    0x42001400702c443d0f100c1c1d40c042401d03130401c03296407032058140031310b079503002109181c40c0c01a6916a1200e003031245205510104000088446040d500380e51400340519017400c5083c0010f01c02c2c1c9c1c00065802c45150041008400d030050244245401400b045401481140c0f460b0041151503002400c0349040110020009401d81c40b924901c0c1c0d0044007056010b65100d00d4560400d442d06428051959204420404210180b030034016921540701c488025000c000210b604002528505000d20829800b0901103028600303070603c030951089000e900d03881c1e52418031080d803031329010a40003900c1c4603514109064080c0c0f111214100f640924906243d03a907501c0d400001900c80e03000f1064014185428004c0d41c08010b114100c881c003c4500c030004909642e22420155018051080390702d401c0908410100302c0c0c1d80f070614109482107205400000ca0041000040222104078084140800e03080741e400c0d24120500000000185110110155554180400201040940114542e02104400103000e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 457465350 1250 457464100 457464103
    0xa090228063c021f1b0203120a090201110307030e01081e0a020a181202150421020a08100509070f060903080702030f060106111b0616080c01021308010b04021e0903 72
    0x70003130700302c140c81c031440320301110495000b5044c0f2070420108203114042c05003150b800001910501d844000c0035040590782c0c503007884020166414140d041200c583c0820201c0b0500703000815010740603541e0a0600c1c800c030000034084200c042d02e60000348041e07409022408a46902540e00220951009a1340d519121402c03250144a1131402c0c26845941c880056904004221740300c84a00c2a1442d001c40c803649000105c0742c2c0168804c4084154146000c101c6202e100c0800e07020031403008041c662a580c0301d0102910b880c0c14040000c9200b907a0b4014880f4884003089810010304050180c40d45103803c00c1d10080c110303040d52100800c85c080201c0d444045560a109031500400301070304403041c41d0fa4407240208107840d1903103034110b140510140d4407048842d251440c419404050304044c0f0b03081d005242501d07860700e48607095624280500004140c16400c0c00281803c6030401d0104891508086415084526002a05101d14410840c2010381c11031204010708807010004c9e03003603c9d02515000b09 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 457466600 1250 457465350 457465363
    0x10f0e100f09080d020a0209010603050f13080d051f05090c0a050310051002061009020a05090118051203070c080601050109150201060b040603090b130206030a090228063c02 76
    0x116402a600800c541380e0340002c0f0240994004c990341210350341d070f82000340c2c00c80740190340361143c0640e880d0014031a11440800314008a02c00c4140a1a000a4003902c4080721000d442d555030842151403078550704541d140224000d0041101d000d290b50a00c441d40100d284100008c04041c40301c044002600540141c007a0001007901030304951059106810082d07d611084844200400c00104041041400341c420b681e00c0340001d071211460704030792000655a001a140c0c1c840b0451040d00c0c0042207580358a040d0300c440082e03600c02140c0b541424500024440015004601150700420041015a034020102003c8522506406401c0d9911f41d504901401568108001c1c402c2c0000b40042c0590341a805514010701034800d6844940328102004208118107802a41c0404140049014111141d2103048107071701c010810701e080803d0281d8159a400b42000f9004c07003806c0c43d00e007000116001542403140c10300013007074448400a0f05100c4920750800154010380035804520103940207000f007108 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 457467850 1250 457466600 457466609
    0x80604150b0a02030408121c0b0d0c0e15040b0a12021f050304020f030a02090a0f02070f050d020d0c032304080307150f020f07060e0a1202030306010f0e100f09 70
    0x80b50344015403440690303281e0042c03269a141d84246442e5500b010b4600081e280012850342d5442d04000c1110920405081c0c2c20105c40d81c050002180c10001030b0250b40307480002c1440d5112901c140c64030403031381111030102d903a0440c0201d0800c0005c2103146e0711000007605441550000140c00e04072030004c69001d04c4400c051240764a00001c00c00140c982100186200d140300301d403c40c09081c9a102856100e4000c060000e42110342100031441100e015008514030113880840141041c0c1c00303840d0501d0800c00700806070741640090340d03a4040e0f50703814040304400109a046c40142e10a07683d0b802800181304000070001d104100e0400e445141c1c9180403200280103010490361200150304090b840fa4404e8440c0c000e142e4070b004e00315500c0e61024025070b0100c2070307500062820f20109480e4400038256050a850250184000001c0002c803c4070783c0520a85180d4003c5807245880700015080e149480e40700307001d0000740c41401c012aa941c1c4844400f02ca214a015412100461419504002203421 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 457469100 1250 457467850 457467869
    0x3020c0c2b0c0305160b09100201020c0102161109010e010e040303020423090a15090207050309031603060f0603120f022d0c09010501141e030a06080c0f0108060415 72
    0x4006010259070240292405a410f8079101c042004104217503a14512a486050005020508607481e20003507012600c0a2030001500e0702038110b040a08a0340300e0160051a00581c034046020b0003002c10170826603000a4079041c0300ba5040140e14107501c0c80c14800c004071680d485000400b0540300390180c600402c00d6025603080c0b0a0018001c1034400e9001000d03c1c05000e580c4002620000c0c41c3c000c0303c000a8540418040e0b203800d180711a0081d50000390305403880d2100700700c0120592020081d0a814900c5000c000e80d0040c210315250b4151020024407450f020300341581400402d4001818118415013403c002500d04681c2100340c0c01c00a08074115805540d445a041d00200040c0711913110380108081a12403c0301504204512088280500790000b5100300b03810001c0d140742d500034600b1a1090b01d100390f43c243c0040303103000700f42d01c101e61282045888030b0f001c1003034000400a2039040748044800700710b20784a040008209280041200307110b562214000800031403500c010b9006000c5500 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 457470350 1250 457469100 457469179
    0xe070b0f0d060b091207210c170a1a01080601120f170d0e01051603020309030c07080d1209030e09180313240903060f0e0f060a06050103020c0c 63
    0x2804940f00703401500255008603101040031580190200e421010796a0004000c40d0403c0d0310754602c07901440a28084581d19480c841c045000200300230340000d1290100c004060105241c540801210b401600010703460034803500511110304041343c000d054850504107442c03401140e040a10b10307060305c0c520280c05602c9072038122654a2144c00100306200040c0d005001180600b01c4040c03c84604541e0b0181030710301981c880c103801e8445d800031600025050b0440e82050a109552802e002c0580c0c0308900c26800403c030502c500350414500c0c0c41000c201134040001c071074292400f40c411040448503178866800d40340010385400d040b00c90300124282d100c003200d40b0345044d40e400b0203a05005005002c0c3d4200d50000c1003035071020410a102d0600c42d25610907a000389941c0d1110050044040c041c0030841c0c0703070035180d000000108178801711414020b00a11180c18201220b4040f1070032600054101401040900165540080c0f070140c10f203000c0d03420380c40c140c4691002d01804038070700c0080300300c0a0080703 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 457471600 1250 457470350 457470359
    0x170a0e04140f10030816060605030d02060a11030f0a1e060308030105090609040503160501060509090a060b030d020a02220929041104230c0414040e070b0f0d06 70
    0x18219075104900510284499440ba001a640d1500c00c0d480002d114540400c0307944070810b400480d10351954800d0b6004900d45c0d448400190802d14410030303d20059020100300f2000781218004c1c54043d042e0804124918108810901d0604070010401d001c0340e9120580c4005048054010118940280908100d15030712840c000c142c40d4420302c260340c4030710803640c0810403510380700414034051a07110009500d412680b140142003c3d020390300a03523095580b2880045d0316210141e42c81d200d0030180c40503203040b01c0185007910440e5081c1601030b000ea8805040c40807103075000504403140c20f4045407030b03502e102c44a50b05ca0108000b80c401841090307050841400c10402080b4500c0703128075030710000d4684801d044590503110f03042142d0140143c100320700c0d01c90503824a940708501002d1000810141d048082405004020045e21861607030440003904114075002d480070000245012a42401801c0b00307038035420703070794106801a454880800609540c5501802c2d040f6414a44142ca041c08802d55a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 457472850 1250 457471600 457471631
    0xe0d0f051608010f0501050a21050a240501080c010c0813091b030b060706020901110f0c01091202030d030e03040f060c0c14130c0e0436170a0e04 64
    0x140300b102101d6003004200c481914880c0103140c142d50002d02060b04452601000d0440501030007100d0400d50302802036000428414032031103010b140107401c900d00340c65a01c01203500602d062103e10741a180b621f4010320141d0804501c0c541d80490034070303026460903103908010780320f849401e01d00042c0b40d2044800052030426600b0444072808440e00f000c007903140f0f0080503030a982d004003615500a004007c000006189640030303120390b01041c5030200700520a04401d601e0b109400144040c00e03440809074070607540c0d1200011010705228801803215400035070219960302c141200c0ca4051584030305281d034600c1c00400030749008041008200c90074555030ac00c05000c8803003060058501c24040d0501041402401503040c904050103059210f6640340c2e090a1002401620454020030007039030300c0e1030100c0e0345602654000120207503070740240861000700417035030045428560003255030f40a103260104100340c01200300407803003004082d03039426003500803034103c05500c1200741d101d031034402004039000700c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 457474100 1250 457472850 457472893
    0x20c0118050703060501060801120213321506190e09071d1e10050417060a18020a091503020402040e271f09050111070605060d02010e0d0f05 62
    0x84c0030400c220b13606c64200311a034040900a642c607140a400d500f00041c102030312a101c0300d0b0f07107080c2d0000702d40c6140744c0d0440c0c0400e038282c14a004041480304403121a01c00b090349030b03081f0407071645411a9021080c0451b00c1e40c000c1c035a10007030018107990740c5200705000709811014802d000306038411074a802040582040c030b00d4014180c030310400100c16420ba08044402006005421444041520b4050200071541c200b903d021420408284030024400c0301208108000c08101005071120f8580100c5060440d100400680c2e15400111000700140c1c50316842c22090700c2442d1790100b4441500c00c01c40b141203003254802034019100141c0083c4800c090851240101030010fa55202c0451010b00c5100030f00c2c04103020045900005200c962600030589100c880444802c03021820380c1054407010301b16400031060358400036000400380200016071090030b9005100725280580c0100d2900024030444013410518003d840c200c200005010b0742c4450144540d0748901210341d00c00031000c0c066401d40 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 457475350 1250 457474100 457474103
    0x304080d0518041e1b09030209092a12060408040b180d060603050d080405100e0a021e1302070f030503150a150e031c03050c0c010f0b011706010210020c0118050703 72
    0x610f0301410070100c604d20170b400154120b03503a030340111090840d000c100794013801500c950300500c07034a002c1c41d5110000d2010441d4240740c000034003084156036801e000701006401b030310040d150041d108210009030304e58142d40944000d841000c1c2c54115800c2448904001c9409599000d40c20f00c00740c0c01044025009101502d1081b03080d5419510b400c10160f5001d641a6001402c40d000903000820040c0190b019054050002045445218107600812042001c0c850344450320040015140428104031038490140420751038214900300f1240c95036110454400002400c100000001c10038420842d40041d440d030b031000303208608440d52100788850441500110101145040d400c4840c039140c0424001440b2002081141420003051000c40041c41d0017820120200800d01003c0c0c446042481248441481030704002400ca0552001500f02204004028118070000040110303e9030302103500100b541c00b400700036854a00c0400e1039809003101146003013940c030394141440180000001d4407011039 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 457476600 1250 457475350 457475411
    0xa11150117010b0d1415011205060c03090a0b130209090109032604060b12030304050d031b050d09080c160504052d09010609020d090210020304080d051804 68
    0x8401401c10707801c0e11030186840750302100f0740a43e0004140c2e0410b181001d0740c0c103e42a280e001c0541ca0b41841c03000c800b0380140f0300021300e400c07400301080002c015079130b0012003103d210750852410101c01641c0c6c000390fa50050888a03810701042010701e0350320a001c84c55030b0050200d0103e00d0a40c4249000384603030300701900010408801580705100c64401542600500c401d05603090f5980d03100d03031002c1d100c5202c0e00c541007611114003100608040c80514000ca1144c0b01405020b880a00014103691000d40949265100c0b0800c882c901c80d007040480e90048040782010a40c401075040c000740c940940040c00045001d5420910004881c0d0500001651001c40f010082505d5143d120080d81d007241811141003060b00305034521320b542c80c05032180e00c5849180082040c41d02e4a104a0680c3c0009451501454551f1166411031070b0980340502120441e00c011800d00340340c0b00c2004e580d080c00765100b80c1481000201040518001c02c0381500040f070242c010b06c00100356440fa5203002c0c00303034800c0c903058 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 457477850 1250 457476600 457476629
    0x705070504051314070503190512030c04060f0905152a190f0804060c023109110603040308010f12080a051b0a0516170604080a111501 59
    0x10351400703104240c0141c0200c001200005266900c00b600844641c01c111510f00c03840f0000074082e601040000c009003c907600314010041e44c0d2a21500e404c400442d018204c01c0b0070310405c551450381c070058804403120f501d020f800c8807404800945440c02d45420098000c2d03401d07405c070444895024020312408034a00300340001c4200300c00c83d84030342e00c02d082e41c50000c0c0e8200580a02070b5604000344030a015024810365464070005590b6031056a0290b404070010070901c200c010300303514000140c02c04000c0300c001c50141c0d404200004000440003455180c0056035900c0e0017400780100e0580d041185031003d4038684d62400d09040c00303481070400f4810b550050b00044000300e405460482801040713940504e205081201c034403010b44050f00030b1000907040c1c80000e21200c41c4902c04201c640c404500400c06030440007160f0a00c100303412019084001101d0311030340d074101c40880c00244282d001d5005030899807500031400007180d01c1e040c503a403080720610490742c204d4501200c40c0300f82d504031580d6140b140c25 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 457479100 1250 457477850 457477859
    0xb0403030e0c03060c16080409050405100e030c0d0318060908040e011a03010302040203040305070807031e0c05061816060504080c040c05031306020904020c0102090f03070803190320070507 83
    0x140c55008492005d02d000c001e000401e000c1c8424102c40f030307925201c0d9000508141e11145100c0440b8022101902c0c0c2e94040403151150900c9485041c010b0400003000d5032806c901c185034a036a40003c003d0f42c1082603642d680031000004410325141d002548400141706440f541c0c01e04231410341090051403008038500c00009400d03210b5040641480514091b81030070b681c40c0d43c0030400207402c010800d5051000403c00640000c020a00130424a80310b0b0f16003250a202d18071005500c118014814418170603040d4204000c104002a1241c4c8003038000e107001c00300c040010311541410000190b0360010800050701060440c0c0000c05013054425072811224440d61510070001510031026911000c20010000b10ba100c010049054107164000e10026241c1840b00020804036400080c1c0c10906950200d00c68034a032500011301e0103030b0030040300100601d40c14502c1d074944a1189001d178001e00071041092500b81030094000301d201c134968500034201e5a0301b000d0601c905a020102c11a8180500c240208 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 457480350 1250 457479100 457479103
    0x1101020601031a0903131e0e1320040e061618060804030e030f01060306060801050f010b070c081212090706050406030216020a1409130206090405040f0b0403030e0c03 73
    0x81c1280c0d04080303000c110b0b28500b10342c40503448014003101907034007040218000c0090003480400007040301c0d0700c0f60601c0c0d014a0800260854054000c20141c2e80b001c024440080030042998213816040039607498180f0041c5a400024106500802d800c54182035609a0501c4080b0380580300d441d0b50081c00c807510100032021a1900301d541007119100050381418040d8600c100c5444d94485d219040844c0200075040002c1e1411483c1c10074200c15039154a0140108480c5004060040c1200f0000303005a080a07030789511303000310501400502c03090100303803002840380c5e0f8200781c802806004280c0392903400644603003080740d004000e10029140e4000208008400004480c0212400b5030f8496003040d0414a0460195200b1100140600100e801c924003680c0e94508a10090a401c94a988a00b040e40184013682400400c2c00d4500500709240d82c015072181022114070000440c0d0028075640d6030301e041c543c0641800d2000e400704032054204010107405a101075080c444041c101e550282021b010135 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 457481600 1250 457480350 457480363
    0x10506120309030a0b070203070615062606060a18080106091d0c01051c020c060124020a0803060a090c1812020310051512030a090506090f0d150216110102 68
    0x21030f0554041900d01d0b01044400c000682c00c0a02031055078540341c403644821003900e24000b54000132110030300d410042b0a801c4040021103041c0070690400c0080c4164400f02e050038018005c40c0a108002541690148030b03200600c0c0340f42050050640381511551454005c00582c090b24282901d0541811440c01e44915131110101d8044001c08920704001e0044907240c2143c500c012600c81e00c15641400c4168130b0000d03207800c410010080c4102d600d45800406a1020000351481e00c0c170078840740b100d006501103001541c0303c1d001140e50303503641c99180200d50307003080e15130041e4919442d003003000142651100e40703120004214203000c90312548540340d0f0b6103000b0300d00d0b0009505600c410a90f01b0003000c1c582125922103809104001030880b04c0011551710564540c0e100340c2908001840f401142c4c206208801a110645d1098280f5000c140420528114084118410040c4800c100c0c00c00000d80c41a04c100c4261903001c0d074680080d100d10007403121105070225440b0020f440038084651000942 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 457482850 1250 457481600 457481617
    0x70c0f050d050d0e041e0b0906010809070603111c09060e160e04050a050706080703140105090601030207020a0f060309060b120d2703211103040b09040f05090105061203 74
    0x19001800c2c1440f000e40f40008a844035039041510361844504e40c030b1488020649140c1404004130343c8040481c20003004c0c140060800381888010000c2c13080404000840c1c6080d40d03083c0c2800144861800f1400182e8040c1e8406c80d4480c01c6003101e1006000c44640003598124440c540a1060000c20006242c0301e100621a0058000850804110320100c6000ea250001c0c0140251980b038007040d01d4080c24686c02c0d4200401080c48401407154156240c41600741e50024003180340f815504100010310f0041018140504058020840b40155542d0040140c010071498001080d41941c0d5000507004e002d5041c001c0c1c440c58a03203c1504201d09101d500d603d4043c5211000e0000304455400607181a1008618040940b44903d070317080000001040143c0a1401040381c4028046810603030080c0d100e420b0031100c200455010404a851700020a490039501d1500d482034a45d4260700114005017003440b00710510a05060901140c0d01042d480603000c0c1c90207481d40380403840240d4105075070b032250025 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 457484100 1250 457482850 457482853
    0x30703110316030b1603060e09030301180203060904020105030711010e1e0102070b01050432040b091518190609021503040b040605040614160f02070506120a0204030206070c0f050d05 80
    0x800040070341c21002c00403012400c0000347c09031611811600c2d524115007008003035000100511100d103071209140000d40c40b180d81940b940c42d100d808501406d4010b04004e06104001c00401c0742240241480880001c001c0e0007000721000513075209540d40e015150f03400ea00c03800600004805103060080b12880750704070007028440e901c0c0c8810302c80180f042c0160a4a1a010840419034843c1004101000c4104c0308451162a04050804600104005c0d1900e00180d00134110300e2001000e89004c190700c500342c81380a0840c0c1c000100d0b180d050211600e01d00d080107880c00c0507281000b41c40d60201003038500903624001041510500b0f041d05210035100035041500850000d00000c0aa41055904c07d114400204140744410f102c0901301e8400d440c0c03111400d1010084091075940a080c2141c025140d1000784a05840d10f400301d0100e2050714520210802031030005030306004036804682c0215400303003110f81c0d1607080e030905200000b4640101c1c04031b50304a42c40010b0624041d10100d845640040 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 457485350 1250 457484100 457484123
    0x304060203090f190b0901030605041b110106120305032e2904030b06040b06090114070c0b1b0f0a210315090b01020c0409032c03070311031603 63
    0x82c2007080c8003619441c2c4580c403d89000d0040362850703e2a030200c0003070802010342500d9418102c00501940d9071a0005400b403442c02510026010400310703c50300e50f4031241803660900710751804440c058400340d0445403071a0b405101c80020103a01400039486000003584543c0d025400d1142e40f524800c40c0000b03c03001036000c44083c00b082c081024401c1d04402c800c2511240102c90070703407644143d00103070301c29641d0a404004001e01d5040c50f0241d9911080101d9501d441d181c001e000280a441090680101022010480500b04214540030304090000449803640300c940e901e00030031003014440d40c41245030280c1d41c0d23032059840001a05058140e07000011441207507500301c0120300120f01405080c00c1580307408540400c031000c000080c0292054220100b2001c200d0400a40f078501c020003402e025902d03100300000400c0e400804078540081c801d1a0300b0f65a4001d40410071036a1103c0d9419500d1700855030004100060362515004440080c1c4c1507910945800102005080349031001510500864 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 457486600 1250 457485350 457485367
    0xa0c060f050903090411400608090c0103151703040b03010e0402030d0908190602120406020a1403101202061918120c030b060109030819031401290c0a030914030304060203 75
    0x21f044821001030681030f0074101c850549402440e41a4940c0300c0004a24241d05001d4111800c0c402c48100080070b080a002d20216519488510350032407285480c102e0080c4409441c40c50144115070061015542464076561103003030810000200382ca08a20138400c500c04401c1003405084954111408403018007440344440100c0810060361100440e4015403c00c060030103000e9031741d0103d000300d024410058503481000350142c040302c441001040c3c00c96040c0100403001c540c001c0640144c500b401c1c203182c121209480030034414000c1c0c44418041e04910003480c544140d00c000e1040118600c540f83d86415980d405841d603941c2080c0001030558a030f002130903c041800419000d41015044c989079114a590b91a034445580000d4030358480c0b070042c01c0c81c650449605002d010030ba0316012807061101c0d4174040844078a40d00362091400c182d101c104916100d90ba94800307503440d0002070800c0d603444181519000b0700d40801d60088121751109055140001e04001081e40c2c180c0305907400651400421 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 457487850 1250 457486600 457486657
    0x20a0b0604020c061003060e16050d03020a1a0f070c0b0f060316080a110103050c041a09090109020a08010602010510030201031107020402070819140a0c060f050903090411 75
    0xc1aa0360041e030208820000c0000402c41c89101d24680458001203a05501e408821744044080c807142c603a000c185404812500e29600d0f03012602d084880840120107881c040e030410b16100301c007910b15640f403000404116480b010f55481403050b102140000d686121040c0e800003600031019000c03220300400294184000d000c0d0701c0e0010401800c0750001c80c1005402c4440300b03070640041500c2e0304002644020403407a40d0b0040ac41c00c0f000d007828445480c0000c204881801903101d100080329a1712102d200c1c03148100c04640324140d01502c040b50350742c1c45010010103540802d01d40e200140745440005012071041c8075050144005c0501500203510310340044019180001288040c00420084040103994a100a00c00d507840703124903a880d00180e581c0c00c8004c3c5030301841c1905101500d0510f1088900c1031045891002c81401c200815018030700700b0800030400271640083d01c0345800d00303111060800001801e4200e4045800380960b44031004c0030340031030059000d004000c2068807120400c0070304 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 457489100 1250 457487850 457487873
    0x90c100507020f0f040c02010f140417030a06090204140f01031406061c090c1e0e010b0f070203010f020d0f111912020703030b18040309060513090f050601080610020a 73
    0x10040c01034241c1568040000c0481b8030000250002d41c1d51a0260a40403c440c0142038180c0325034100c0312628501600c0c0c042c51654000c0ca034000500380000000c01c09000355101c44003610000030210b441e0354441c0c0030309a820b0f40740d44040b48034209043c0c2d14a6030350320a01030414903c017015851812a2070b0b050501203150080000860103541504103580a4901c61042c030040d0390251065400c1145000c003008024281c002074144c10409900302030003882d108120301411100c4903403845549518601405150b40200e0200035030550070f0101d01e13041110f03140c02900d442c00c41d13540304000301a5200c0900d001c07900c118024900e14141485180703400d0403030540b0000c20003681d04048481d4a07425841070102c0c1c1c080c0c0d0301140802e50b41d5001012a0814151404d0141d4008591814a0070203031230152081401d841070744100000040d08100d01c01c00c400b1a40020205e07080d0902c69050f000c4040d00142c80c0450f031190000304034a0014050b03240c096080a11094650003401c03441291791680c0f810b460 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 457490350 1250 457489100 457489129
    0xa0201030b01050c0318090603061e130209040501151514030601020a0b04060509060c030705181c03020c030105130b0a050403050f0406080a150515090301090515090c10050702 77
    0x1428000c2d1413038000e05000070700804c59070902d0060742d803071041c040062000b4060201c600980c402e60801c100701a03810301c0f8914400948040040d1540c0f445c1d02c2c014400706001000390444000000e00041010541194603664088a2203054141d00c410024003104001210703000001e0b40f042c005050864201c008540280040c41551800d12a54850320b101a409840456180e82d540c0b041015200062000a800c1120066240e20714103004600030a14052071182180241c100f01b840d43d899500d5017952403141c0d180d920a412400118100a519442843c200a00a500f1f2200040c01000c02c2464100300340d5108030060200e4507180c0c444e000409000313100b2014440204101207100c0d480030060070050030103076500a03081c07529a82c032806945041c81480b03080c083d05441030000382c0d0b40b201c40103603401101454640b590a040002805009200b001804034007403101d6802000c0c3d08540c5007131183c3c17081d0044410a00d10300041c80706403501400024002070083c82404010710f81301c141c955480 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 457491600 1250 457490350 457490357
    0x60412050c042405010e060906090d02040f0221070503190e390310020d11040f0509011505030a0e0c0306011518050607020907021c05070b15030a0201030b01 69
    0x180710110202d4111a8106840b106002035543c090882070000522180030340002c2c40e0550b00407402070302144c2d003805014441881a4000f0414801d107031201081c04c2c1c200d540081c0203200b80d040c070b143c040009511001c080c00081b4081c2a84410044003001558040c86042e510380d49503554040e454006819640a1303600401c2d190f916020071080c0800c40c19010b0003010442c0b807500c5031804403c20a90902054480400c80350fa131400701c01c0c2c1e9001c00c5103501548001c030302680e16039104600350020200024502c56a18010402007480c4e044803201800f03840341910409070701d980320081003641d107441b03208410000768100005000c0c0701040e0407040c0d8420f0290100c1b00c2c04184400000d050a1090700290322410001d082c13071010552120300c0b004a05510048180014144000306003944510380340a80038000c50b00100f15124030070403860340141c072403100b10392812035030b0080100581e0010100b664a594100c02107a206110040c5512818034000d0080028404941c01034002d07000040308503050 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 457492850 1250 457491600 457491613
    0x503060d05071d071107140604180b01080c34210210110d0506010c08030106091e140d05070801060b03040507060314010909170c010b0103140606041205 67
    0x4804100070005025880040b140072a81d8104a600c030850013050301e0f0420001000654103400081548002c1c0c070341c20744140748441d0311a40400e005101b5907016080d00d07010b0180c8001c9148142e44048a4130209070380c0c1e80e4050311031100010983c0208454a080005013450803503502813143e145e82c011507014802512911500d1302c0b00701038080d1910001c1011010a03410f0080135030706001d1850680d408140400078100141ca407848180211001010b0320350b52100030a0003a8001c07040d154446500c803038050b42c1d03903071a030300001c0442403544a103a11100b50400c110020030804005032094540301c00925105254141c10007032864002041aa418000c00d9004900403c00b80505005041c0071942e6541e2801c00385050f0b8038110032a40424101440c0044038008604200c01650442c1c100203004224030440c2e00b0045100000c205001e1911070000a07103405005064000143d403c0098908121480c1e8405907811461400c0323030000c3d44003a080005011500401c0080e41025000701c1c1110314 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 457494100 1250 457492850 457492853
    0x92407090b0c0607020106170a0308061332240d02060307020d0e040504051903030b040501030b0708060901030224120906090d1d130b150306040b0a1202010503060d 72
    0x203a682c0401e41802c0c00d60068010484102c0d024003411005140e640c5c181400c1c40c800c0c406081d29800d401c1001030030020441e020945a40c0d030a0300c440e5600216400030005144406032100401d0a54501ca445250359044c00702a2507208016040c820002c030701e01078204003500c031800c800303580c10f44603102e13030200f20301c0e98010150f22520051445400c050b001880d0420341414050425040308821500c124200010080060000f1407014070fa8548070f9690398510441d0715064003d01102d00143d5000340c80c0000003c103001c1c21103043c501405150f203840c2440d445150604c0b120140902010350060308101c1101d10a00c000d140642407600c8207a692030500385642041082c000e0706566a810540c0486c0c24045115000e01a070706003800300d07080c4103c24280301802c080718010040000c0e441244802e058a1902c1101d1300000b00c40c0323400801c88048617400c0d4000c20940d8001b900d03010300030342c178000041000b403c184d5460300c280c5061200c90b05041f50030b03500440c1d060788018015a040851401482c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 457495350 1250 457494100 457494119
    0x20109150c1709040e0c060a08070207080303090610060309030207030b0606040906090b0f01050301030b01062016090c020102070510090501060e0f240904062c011409240709 76
    0xa003035815042c060362003c80d54208070aa400b02c1d000782c5c8964102d50310b00c642c41d40e00c0c0e100719051094181800489a81c501d0001d03070401e28503900042c8513000001c20000c00c450007091007403003880090b9442c0c001680320801103080300d56841e401000b50303000120070710224101380c414582c06680206654603050325482d03c00f0942c0c1690b80140274458440110b4902454920101100c1c0902031034824155899034440101010061054005002c07404940b6a220826401c0c034814a00ca0b840458001c29103002085451403440c0c419418510318219041070f9191042c0210b90100350420000e10001c607c254810b002805800d17001c440c25940d40710000f460b96084507100e0311030300c1c2e01545443d80f46000c6000c3c600980418080340001d403c1550300b0300030740d41da02c0f041e95000b5400ca040054262401c011031030904101142c880035031034850551140c2024150410089402c00548200c1c9645400c507811b036807113141100c005811403991070307900071641c0c0541401e03600110514101032030301e42d0307900b001 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 457496600 1250 457495350 457495373
    0x60c0a0c230306042a17070504051306050703020d02160b010e01060f180302030607020a0b0903040308031503010f1b020106140a06140f040303090e1008030a0e0d0828030207020109150c 81
    0x1090300e1006d030b80d070803183c141408603000610064806100c0c80c81d00e200184610030780690002d081e107586602041c01c0380c1c802c0e8140c480c5200d03a58403c45d694003849400b00d06800b0b4010084031001548000030900b04421180d042c100c43c0961110590810409010b68403052090580403100b4220b45c3c0000c056a030802c007560190b020358011b49090285401c0803801e00c14000c00e4170311a07a004220810000e130f004400c5a0340425144425021b1500b04400a07001d00341030b080c102c1da042e08248014844030303140740001c405245250004c00c4000c1e5030b01384882c02c0c01c0c008250325a20407845041000b00300e02a00880b504042c40c549400c0c900154009425119001900194000340e01103e09124500d000f20b0b4030703500036440301201310300c0900d003111140e540c0c8078a454020802c242c8600d0704805484182402c20b000d5404403507a925914244880c0c00c0000c880d01c1c01200c1d9015810f41d4608482c02803084079801501a0740d0f40503001d003072240d00550790005403903120400c0603502e0702c140482e1504e000f6 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 457497850 1250 457496600 457496609
    0x1020f030a03060e090109030e01121415030c01020606030706140d0c0903030e060327010b06030a09030e18131a040c0302010306050f0d0b06060c0a0c230306042a 71
    0x141c00f60800c8085104500014407014990385002c2c1c0c0100843c1e0442044040b00c0005d10740542000780b202152805082104115034500003001c00b440340080c0c405c4031100072094240d01312000020f00c40300490796400e064413440d4043d00200300a1000720300c1910184071030003201134818030700003104400d8001c9402c042c400301c0c002900c031031091042651161000e005400c00321a0300f03055003069031803031120821401c80d509081c131214810103640700d002c0d0895040c0e04002044182c491810302915406843c00c120b00703c3c001200c03c18140a2445c00401e895101c0744030032102d40c181c2e502d0700800700c04580001e009a80501001800c1441501b101100d680314620510750b1000851840c03001505032402c94110920840d00d07113034039490540340e6400482d4840d402011200c1c0544a04012070010312600500e00b070701c3d0007021070400034001c6240c0c0e2402116000d62000c640600c0e1503245d5254403540210090f071581091011a000c203404100b4074070019911624001d03540102e01d44024035030b140741e00c1f = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 457499100 1250 457497850 457497857
    0x150906020c031602101d0103150504020c0705120a030c0b04050c0901270204050310090f0506040305130902120703020310150f1d030c130b04060e15120c0d0201020f030a 74
    0x43c2c4904505008481c40d00400b4070b070030301003012640c640e01c1c1410340c008507140358101580c400d0700b070b400200c2c1345d85140020031016000710754a007412840746031280c509020302c81c0110700041c5064003071500064221441c40d05691042c5018840c1c0c1d4441c5851540a48265460320030094010050794413801c000f802804119040c840c1c40441c000c403100c241050280c0c009131984180001c202c00c0c0c402040c3c80c270303515100101c00103c0740d100b0300d03000040c0d00c2202c40142c05449071504020070940c100b401490301d10010341074091029511342a41d1b041c0d100b070303902480b000240e20000c03d10503800b07074000e903801c0416045101070440d1640190100e0898500f103480000b02c078003000c880c440703800136580d20340e02d00d144a025080c01b40b4440441e07586c000d682001800b60400b2096002a5640c583c82a000084001e00a020007590340305940c3c40304005039a1a00700d10300a00364000a85007450410743e13545184401740c0004405003007045111220444142d06500404007400790610040c00101800c030090345 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 457500350 1250 457499100 457499137
    0x7030203090f070f0605090607060e03030702070b07121d2206060c0c030201050703050c1006030b0901090b01030b0a020f0c01090b0603030403170a050d1406030613150906020c03 78
    0x441458100d0300c02c21101540c010407014405006110a40401d48605c2e05013103680d04000700100e00984200900038110f14a00144d46c1200e690100046004070702e19404c031030314140c940840d0946c40c414454000c100b10402d21000b05002c4c002c1d000a0448514211550714581041001c5007440c01c00000c501003515002c00620528071240c820400030348120700c2d00d03540090440d550352208008601000e41800f20205074a401c040c4548200d13a48040545c0950b1502d031f0728074003e00003402c0c2030301003115403040396800034039001c40c1403146104d43e940050700882c281e4696110410480f001401c0122100d07001c000b07500700e101c43d240081007400c21510001070510500e040c40140100080e01c00c5200750410881040401c1d001c003e4800f00c2d10098181c9591a2283c00c0107070f550b84038a9038109160307420403c0c02d1459000c07150b020303031148406600307442e41130340d03a120002b000702c0081d0b4004100b922180140301c2c480c2d04035408100700320300c211401843d040d0311501303661940c1c00200c00805a402d581707 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 457501600 1250 457500350 457500361
    0x10c0f0b0a1a0109140a03050f0706140c060601120f2406090e040303390f03020310092714010e06131b03020a1d13050a020d1a07030203 60
    0x38070409060b076010455605a000810380020801e50a912420030b010032000001852641e810211a00641d44081101d10b40b41e403045982d0303100c440b244241c06c0070403982d00c13004410007082001c039407a004011000d0546565100015030304216000d1032a00c40650f0f0304c031101e16002040c8542d6206440d040328007080c03203c0007040c08407440c05a420601c1041603810342002400c1080301025041981810041140802403070010824030320040c41044111620040813402003440c40f48072a030000c195201c15840d0300c9078105400307a00c01900c8c0d103c1c6003413141030200000d5820341c2c007444511004e480d104500c044081c80d04155403080f20400c0e40d000e5409070748021400002d1003403a40b82402c2e6805030000785030051001c86440e5010324090414030003c0c1003503c06d0b42c20301040c0c101555004000030040c40c0c03103101d03040701101d884c0d07030a20b480500440480c1c2c044034003144d20324009030721500414110039240c1c04d110a049201604981d09600c010f4041182480c0714a000c0c0b142d0341c541d50060722440c12 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 457502850 1250 457501600 457501621
    0x12f010204080f070510020a150b040c0c1e0302030d090615140307060806210a050d02062d04110a03060e0604030f0c0b0c031806010f05090912090906010c0f0b 70
    0x41c0e51086100346d6420400d002059000701d041e8180c00c0d00002a0b148040400a4600180141201d1158400d2400307103d40029a044152100154068000305100d04030301c0d010040019101180640075910038044819103c0c015001100d0b094413500f008a00340380c40040428801e810b64000e040300d803031181d403804102c0c281046950020101450100c000e42016008111812a60110b40040141039049403d103002c0c1001165041a4082c0890345070702c0d0804402515102d0a0f0b601280820004072015441102e0070b041980c400c622007601160b54445640303000ea80ca10f403001c4a9044081c0074000004200076102c0c81ca81600014080c0a040c5001c0c9801000102003101407014094200c00d00e2010a07010321105034410800641190b0340d4982944202d15103001000040c0c4520450300003003403c016140680b02110002d4407101119201c1c0b200c01da48401d40860022013401091188410902d040d40c0d203542c0204d0181441000b007080c0f51201e2420305d20400c02500c58100315070a02422120 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 457504100 1250 457502850 457502863
    0xd081224040207020604050316170d0e04020318070801272301020904181415220b01061106060105090a03150b060a02060403080a0b012f010204080f 65
    0x10920046540320480001401900c030200c0c4a070040d9030101c0e00b2400c640b266001c0300d010308001400c031440300b24007500c245150aa42d001d040144a8100002038503100d0000d03031905401d03147d4440180c0d40c0f01c40002d00000303400060040b15212048014140000f0007884190040c0c410360b40089002c180d2403119101c40044d400640301000406035402b030101d80c0890000c108106d00c49580c07400456003c130028007901038202c1c01c6070310070b10b000b40b9030341e070a94210080359501d440751043c0000f059030380300300d20b441d070b40028001c80301c4082e0180007509840c42500c1103135940c0c140001c0b00d00242802d0f00c80004e1000e00341c0000000c03980c14036032403015a504012480d4032030070908c1c00c58500301c24030340403031070100c10340c8401450750b0300040089240c0160340d0070007054120701038013858441d8a0108003e50722030301500c055010030040000304002e26500d002d080508201a1240e4039440101c0c1852141404154011008048000e910b00b00c2c4001c02c2c0000d10041c60020000c186501103503c1041c00c107503 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 457505350 1250 457504100 457504111
    0x180b12041a060f04020a0201111c0f06050d230d030203040303050f0123123003090303220f0302011b09080d08040c080706031d0f0a0618020d0812 64
    0x4600780400aa950f81c00f00300c440391010980b809600d0344203075102640500f4030b000050314054800308514110038141c10054000348000c04040c4140400c01090000302c81413801180c1d00700c60822013401c017040708182005107040c900d0100404409507181c0300e500740030030007030a07800298000052000781540b41c014160802802c0d00b042c260b551408000c2030781e1480400807a0340e40b1140401c0d00c40c0a82d503080c10007451049003026104840b44800354240c800e035001207101c80300c2c1e1444140003034100d010800e41c1d10590601d80290300d9500c5861404e958a410502906800b28455280b800060560a0f0700c403880c510a030000b180311407004400075502944220340c1001c2105c202c1003081036100c00145004512581d041660541d29581402030041e0034540206483c0c0c41500e00c0082c46070341c1640203140b5214000d0700f61a8408006215540351115100800c5040e400180340501180c8154800244580010b000700b0046043f94089041e404d601403060f510034030081541e0450200ca00e00e03c69215 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 457506600 1250 457505350 457505393
    0x30905030d0f1d0f060a150308040902040806010f1503320f150321040506072406030305072003100906050603070501021203130c092910180b1204 64
    0x40d6a00340c0c039130b0b07030b9260000c2515803540d4136502c0302074000701c010105a02942d04541c0180d521901d9192010181d07202d031007000c08a100d41000000c3c40e00d83c00985d0410b89081c900c00501c00c90001100300c020305000c00000d4240800301a8400c04012400040210b03800a641d0144491501100721801d0f080000c11003005007400100848550b500801e6075421917080001c80c4d07902c103540b02c400c81018041ca4101c143c015000040c0d640520140400c02e00d011991400c0e002c07007102c2c00c0c002940030390750248402004074400f030007580300042d1501c0d040001c001079070810395421045400002d00d07008550824083d01582c480c50f60f024001703140106076020750240d00802140e450316000070354410500440b0425034202002188181c4c03000d1040c00401380d0404c40c8a41441c0d1148500710041c0b9a1002d464034100c14003160b20015102c100192844090007005121002009030050b24200304c0306000311040d9050700b50100740105d00601034100a0807400c0d0302515481d00e450310000c92031950145124a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 457507850 1250 457506600 457506613
    0x21807051c02070516080d0e011718100608160f1206090b04060e1c0806060702030309040e0d08010b041a0c0c031b011202030c0307030905030d0f1d 65
    0x10a40010440c0e11103200d04140318607a1440c905030100034026000300800c6801541170400b801d120b103042810580d0311140540701d0309981b243c0269952000e48200d00d01040e002501c440e820503021081c60b5210490080300c4000021441a8034180f0418000b60071015590750070070302000b08100805464089100321144801c3e00300020000300c58690310881c2c0c81d00d40d800814004220f800d8001100d12544200c080900742000d103403280c080c0c6845458021644545404d0125054078905007c6080c03005444c0e040554540e4400d0007017a40c0302c0c00003070b070300f602c0108601002b5444038410302031072100600c040c10304540183c00050000d8410707800440039a005102c24840300741c1440c4a903606088040b90f0350382d1685030032101e50400c14002d5026030306000c2d401c0c034130a00001c184415000c0c940b0903138402040300c420906c2e450803030009488600300340800380005100780340a03074801c2503000d0080044a0070228910034140c1038481c10400c40f0811074403001001c0011311400c050700008000c00025102 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 457509100 1250 457507850 457507861
    0x10e0316080d050c1510030807080403030e040504110906150403080406080105010f0522091b0807020106060215070c0519021005040b03130c050301060305160911030c2a0a0218 77
    0x2e03a1045c455810342400b4503140031828072280648480011079000704403d48030350084c24604000d81141c8000d402144000e051030f0aa071030607108007481a94000c05400100c80240284299010300034801c40d084401c080041d291150030001920007580314581c91941c46041c61001041d011040c0d00c100d050100301d0254203400c640060603640e5075241c500550190380c005581c0b000003000705500c00e010462401d400301080050285c2d19280721040c80e02c411000b0b03220b80000300d01b02c07041c51040c4070058000014420203020b4a100c1c0503000041458407001c00070301a11820304002040d00c44209210f016200700d001c50500400d410265036140c28000e0500b4580800c40d9524400105450451a02c800c4040308002c034a034184009030a005c0d00070010303651640340c050b81d100000091990380009042000420311014003851450031070f4204910704549903d84842c895400ca01ca015520b165805684400c81c4440d14540303420f10603900040800c0056401031014441c6200c20b84803140c00550100324 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 457510350 1250 457509100 457509103
    0xb0306041205031306060602060f150f06160b0106090e07030903051b01090b070e04060b090114030a0902030d0e120f061305120a050304050607050901120506010e0316080d050c 77
    0xc4030032481d800d10b80c1d0303659070310b00c026002e100c101030b00148000d01d0700c1c4001c036446500040d124030980401c2600422030320384d07007089010511300050385030b480000e0342480c43e140d080ca0409014190240510150651416036030318a420800740c10800000d9001e820802007450301100da40c1c5c014400e03080410041050b600c00030b185105d8060381c40e40c00781d80d80d2103c0040040960090300156009410802607040c9910001d205500103e40c0c02e00c500e007040c1e13010514168000443d410b201d4161901400b080020040d0003254000900410065507100030001c00741e00c09201c40f90110407a6517400c80381e90002c1d1300f002200440184090f84990102070310703990101000800b160083d00c41c0d01e840d65a65110b140c032600e840010310720b00f9441c1701d020846644140e04140518003843c407410682b1695034a5600454803402174000182c00141c41c1c0c02a044082c4490b40310580140042c904810241c0f508408a8030302200950640d01030395590004104207070b03052001c1d4900d20141c0c50032174035026002c16000d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 457511600 1250 457510350 457510373
    0x8130e0c070f080c150907050609031b0a091802040e010b0d260c0a021503150d11040c0c0507090605090412110a080d050717271902040b030604 63
    0x2040703000030b00e01c0e940078414080c040d920b120141d00226081c050700e102d0000d03403075103041c1da945ca1107100e8040040b4481c0752220654485ca00054020844c2415019590380c450611459954002c501441c010526801034042d0103a11402c100102c12580b003140705200440320381140c0122682d1410304a80e9081d80d5445000d003c50b034001d450026454549550301c034a06c604d0b402101b503411000a2002c003404c401080800c03001707008580d100b80c80034542c0352000340c0d480300311481915101415180190341c548841e040e0180c1d0300404113a0764085180c0041000c555484000c0c00209503403200540c204003080240f4006040700090a00945107810302040c20100d010b44020142804080041c41d0203100d00380450301c0349548011180380380c1c8a405d10701c44a5100c10300b46a0114103200c0014419409101c5c4c1c16025403a250110240c0c2c0d4801d00c3c2c0c40601c0002c15040401d22150001c8400e24803c10002c0c4060f2001408e26400405c1d15441004100c905a5410354001c0e009042000007180710082c54 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 457512850 1250 457511600 457511603
    0x9030207170a060b060d0c020610050102010204060215040602070602121803161103012013090204061d13020310140f013c0c050c0d020307050f061608130e0c07 70
    0x801ca00792001300180c0680212106c0c0030003949000c03001f201e02540080c0c1321b80607100d002e02408191740c54900480c07e130b2241707009110250f400030181c00c1145207090441c80e4018081ea0f801802c01400c6d40e036850990b48451540084d90f0f180300700380b0681c1d0440710484e45490410200a601d000100d01c1d20f00b200ca80f040c60041c1c03420b980c204072042c45407070039005400c1400b904252829076110164503050640c2102454500d9001c00e101d0210b0705010718401c4a042c2c580c9522110251000b0040720050042c002280c160440c44180034000b00341d1180c005140076003480f04240c102d260402c42c5100c24071f0700884817184100340107002440103036003140030f80c2250581c0c041c0710890200403c800c41d90701a05c200c23080c40281d0f20174106141e02940310140000251040c3c0540d515080b8150400690032843c51029525820182d0208011b00c0d0109040201d4a00580f0f52404c107411068004280d58946800762004840018420804426848000080c1c64240741081c440c0c2481d01c0002681d000f4440d0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 457514100 1250 457512850 457512863
    0x110a030e040c05090409060207030813110f0301200c12090a090b030a051b09160f081b0c0f0c0105070c092309071a0c0a080a1b030309030207170a 64
    0x35182e104500c0b500031541e0442001d40b0501c421180362408800035441030205500192100d80490748006400f8086540d4a4005180f48403030039450003045001400d8a4229038199650030080c803070341130001c0040d08880320803511181c8403140d510304642400e80b100d07008070203003e0801400315203030345103611641691000d000010750310424502080c0b5184001c44060803034480c14421034407003c0a0100260454001d40c2d50300302c41d07150b8511440450046064043c08106510b0707400c80311605ca4108503a201c0400081000c000c0c8003d1b42500c0c4950000725005641d40152139645540d440802c070270900201e0a1030300030315200803a20b80c01c00d42d50950050354002d5803a034041c5011b40c1e0001609800c00320890501d5126410000041a41d0343c03014400c650001c1103034469010340507203100580d80e50001a001030981c07020325980d103581307581c0507103501004d20030602c0101c3d0705100e4501041c03551a20903140003802640f1410060314000d03d078cd00003085030400356500d0031003140c040362100c04140d0108 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 457515350 1250 457514100 457514111
    0x7050f06070e19151b051f0623010302040519080601082113150512010602010522021207120c0519030b0a1e020715090b0112030905130b01110a030e04 66
    0x10840d0040000c5d031041c00382d107000042c1003051000114151400131060307079100a00d1024007240000780d070044e10030031414004c24804401000413010100840d007030149001413400703803143d0002c1c01040801d0001c3c40c03a0311000304117000b42e000802c941805041c100e00105030710040d0407039059034041340b0041024031240c00302d581801202c3c80d5041c074010f060f00c4002e480c145103103084010041d4005510140c030200101e400000c0361030040c0300d504d0190340700b010020a5159040401e003002d541002080b07802c45004421080207180c140070350340207001200d103402e1100e152818407100f0352000750840c82c403030a061340c5400601002c2c281040c040701d86c0200040450b5030f820521134010010100010940074a1160208161420f42c0c02404443e12881031044101e4510740e40e141100e490600040c0360205100041c044000d0745000121640d200b490000d086945500214148290403801c003504a17488003802c0a942d81c000101c000c420001200400c000380803134900410500c40324003910300442d900c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 457516600 1250 457515350 457515389
    0x6051e1f05101107090b0f0a050a271107020a14090708071701060e040621080f0d230c070302060c130803210106080c04031707050f06070e19 62
    0x755515101105404151101c642c0d9510248014050740f0075200d214843c0c0010100c1c003458403c0d104020b03030f0f03406041100740c02c1c180f13400064403000200340300c14105040310048180c4002d80c090f011a4040e00103480f82c58030073790f2051040e8402e080d08000c1010380311080b02c800a841e124945944011a46482c0b10541c0700d41d48140c0350680707500c81d1440d402c10080f00100c2c0160704036000c052010b209031400c004003541c8001c002c00c101035881e0b2000000c02c0140300c103004a42c0c800054800030b0300c0003400d24502511601d104040706c524001c0030480c440611642e50983c1c51103c03000382d116140c00b140600c2c0120654000f915042c000f00782c509103070404100c101d600b85c40d00c0c451002400080d402c42c0c0e0358980080c40d0f00c1d2050580c0010400e08a503100011803158810078880d402860014000c030304060850707444060744504400c0301600c0c0d42c0e045c410540816000c2040c203108007580d0019142d43c4c208502c00610b822445052107000f0040d00621030240307454680400216508401c403040b044015 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 457517850 1250 457516600 457516607
    0x60705180112090c08211b160f05030618060601030906060b04030501051f030c03080915030406231302010e0a0b030403050408060a29040906051e1f0510 67
    0x15400b03402000c1e481c003580392003081090940781e030030b46102c0c0080720458190015401c180c40c040318410703864418107202d40c80664045142040812080000391900140000900c660b0351205501c54002428408020030041c02d050000c980c2040c800d82c0c2d0541515400c8840d969034140107001503040681e11190308041c44502e9001e00c025107414000c1d41e039517560b00e0410038003802054038070313901000d0f0070243c20307807140301641d0103a003100d501001c02d080c21451a103c1e0710403600f208110365001450583c0c0d040b000c0001c0d06c000c5202d140300d10030003d0721802032400304054600598415008200c031409102107903907000b100100035503091a108500080d13490200702c40c106158060010042c000c82480200f6801001030801d4404480880b42d8540c0c81a4504055800c10320500700c50086002c004c180d0915122442608081c01038804aa040525030380c04c02101c00482d00c201030301d1001c4c14819080d03e0300180d02c40d0801034205004083c80350401e42558020020321a0600c601000c090841c40c4501 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 457519100 1250 457517850 457517867
    0x905030106140d02041e0902010809010905120d06180c020d0905090114010c0b0a091403030c0f18030706050c101509050402150a081512060f091603060b0f030607051801 74
    0x820300000d00303250501115009000d1f4140c3c22408109420006a21210140b041180c1d40d034004005210203c50481c8c02d2010340e0141418500c400e413100c01c04901c2c047e460742d40404a0228100c002402400080d000b070400002c291360304100101080700304010b079900d6040c075040d151080500507a4102c1c110041e1010b00c132511001740002000d0003000f040c0f0941c0c4d40401022401607444851007080e541e1556164402112403441056041c0144090b40e02d4543c0507090451004410303400c8481d145002924108075a40000009800014100b84040c803d1220a80a40580728103001c500e22080800114403018001e40d1950390b81c4d03600003015551164209a494810000d40c00d0380c40402590080070001c0458440200c00f1012201210902f01180d00b4000320501001511003900c6030042c045030550003401c4030415226000f14054880685c040040003544944400103807203903548107010110950141a91103a08000c08000d00141c02c074003114010101661002c5210001c82c005036403944 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 457520350 1250 457519100 457519121
    0x10050f0909010b0d1d1b0f130507030e0d02030702040b041e0509070e15040507180f0801051819030c0f0b04110a1a0f280905030106140d0204 62
    0x701540000800c40d07601030041c4203c0d04000030a1003800700403041d020140480c012400c04c1540500100b0300d440c25256017880b02000000e000310f10140321840080c0d0140406c3c03550711446951441804080c940600c90204824940710140c0040c4003240000b0792640207401010f402240c50308110754496580394054100700e10050f068100400b55100060001c240071201b4515a00c54034030302040f4546032000c0c1609c98005219510410b804020a01c03029081c044d000100b44400f0380d1360b40403c03407000341000d009404a1041103003000d141250300c40c00d540d4050f01c4038203004c080b0b40034940b03110740c04a1540031a01e95800b924017551f2907480d00b00d589214000d0301800d01c00341048480c01304168500e00a000e280030f2400c48a036404190300b000241c50840c80352825020420311340a040e800401c01824a601c12f10301c029040c9148251041c84140081213020190f054400202c1e40c0d030741d001203503200a8001035000b00001c60a029070101c03d2814031540301e100e01c01030744d2503104541d95604840101c2 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 457521600 1250 457520350 457520359
    0x30212030d090f0308090a2301090204020a0507030e06160b1504140a0f0e06070e0d060212043809030d09050309210c04050403052709010605030610050f09 68
    0x1d107242000f001c000d000b15000c03030001c1c00242c0802c00854001031211181a0010303c1044861003040f03150801d90390800f00c0041c41d549130703214000903984078030280c6044c20681d11403070f50701c0f00300d0b24004102c2400b2003075680c4200002c1c4032000e905a85841090059940a440701a882d11060403240800c000005219030050030080d400440101a078940b41c0180d101407400d000d503000c1800740340140c905840d0544000d502600004140c0b52281d011401603c80180100ba20640f40e80c070790a0590384409242c00d6016000000d2000700000341c2400e6000f00c40d1a103140d011404461600d070103a06900351400d000003121030210b1100704c010300c219014500e0002c0d042040300c1080c50b10302e403a40c0124070940e10650314410700d880e80c0c06010030300510044882d40580091020f401c101710044c080a00142d0401c14188500302e0301c2201c0c03100510303404200043c1c81e0301481104007000801c40701600560304200c01802400700350380741c6260f0f60100041e542046038881d142060041d410b40500384d20240d02c13 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 457522850 1250 457521600 457521611
    0x40b0c07170301090f050106020102091305070c06021306080609090a06092a0e06040b0604030605070302090604082b020c09040203160618061e0c0501020d020406030b090105010e0307030212030d 85
    0x40c0101c42d8040f80c4696882a02030205230f82c0ca5100f43d0803400345030002d581080720041c40300c0c00c004d43e0f03a2190b81d0048243c01c044046841549912040380c00400c1e0030702da64254204103008075a040105240d11000031100d04166207003950549855040c030810042000e611144080100084280400540c07113400300c1209090b03078034855003110403c90344514940c42404802107800360405000d07034400c1c4200901034a01e440e00d50b9032140000d01e03004011404060f4203012055169a466004000903c1400000c0556910403000080c1c0030300d00f141c0c022140c100100400800d0742d0042005512484100d4906000343c1c1c650001c40c2c00e1550301190200035610715500814044d402c5600c09139680424001001002d0f217030b100c00e880704100800c903c09807114400600c0b1b402c1e1311610500c00e02900c21070015090000d00d403001802d98001d038000c3e0021a485034030601c02c03420302d5000315004110902e400c04171110301d00042506c5e5107207400060f000e41030501ca40d40301c4a404202b203c0da00d50022104101c0b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 457524100 1250 457522850 457522859
    0xa14070b04020a0515220b0f0d0f2007031202160b09030a080c0d02040506030f0403180b03180c0d0506040b0a050610050703120501030b100e040b0c07170301 69
    0x90020040301d0403442594115000301e030f03d040c06104c04902e038608142c201e16250207402c0030707421207043c60b0141c0384004a1600200f00100464050040c003581c503114252254a9581da020903601000381c64984c8d0740c07500046209036020040d1170200003007188901c0795103120f20300b0210f032920040d50f41e07104294000a41c1d880254481d00c0c003110414013a5030044201d40390000e404d40c41e03104e9054043c00103030381c04000c00c1ca18400344004009002504000515040d40d80c0c01055054004440312044080d440d410001415013052140102074a1345a000e0f005074107248500e0014080503103a00c400c20080c012100380c5070000c00004000780c0000b0701d0240b04001a141031959008102ca04560100140b8041954201d03940141c50160030000d081400d04420020100c841d03401c0b5042c01e9041011903004110816054840c290196000751119a081e00d030002c909900c00b0510f500031070000c8400000c100c0031403186450352703400908500e01c8a6886489060500c1c4014100b494462507800000000a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 457525350 1250 457524100 457524113
    0x705120c0c0f1f05060111070b0405010e1921051006150f080402101707020703030e060408030f0d0204030822060e012012070c0311040915020a1407 65
    0x8141001401c4411104042d003140391100311041c80742c02d00485040220084424640029038049010316100c00941e004100312071400581340d0144442c0b981c001400e01542d42d0221002004400944803501001c0003d40140c601510900c180705c240d18200b112201c444100c0740c1c4100183d0b806c80203c48002c80e400c800e1074010a51440340c0622030440c495607249450040d4040169442d054580300d0b09580ca40c0c003800400300c1c511060104014118031802c8030814003001da00e0081030b00f07030b00400d040f81c118900a0318640400c20300ca44640c5085c4400c11400c4030000840b070a503021149034545440c3c0900b14000070b0f01880d000109003443c0071a45c50054016000010300d000302d03500241d440140e898400350350440900c1c94071800507506106601e1417042c0801084680c40482d002c031030856440740340c0c81d007050700a860700716002c0312a00e5041013400316201500001c024211400c01030302000e030392241d00885d454061501c01640100b2041c100c0c5010b09090b007032400030010391039540ca82500d00780 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 457526600 1250 457525350 457525357
    0x70905060f041b03110708040e0f330a080102030705030708130b060603070c021507140601151b020a0609090e060601020d0e121e06070302160602030705120c 69
    0x380c000c1120514016181c070b043c3c02441000000c050042c01181020182100a0034100d507031100751032810055040018110f400a0000340a076074480d07101410300c050344040b10b05010740944d0718819003100c84141c00708200341207800182800540040071200ba00861030f12443d07039000c4031980d48040f0070811101e030040011880381c01a903aa54400355070b6108029107142e40000090031110b20a000075400341041c2006503080116802c102c58020042e6000424484506070321886100011841104020442483c80500c00381c04010340b02c03941c10f0885004091011b49184020040c015100b4a104040300001c010396940191528070b009407a440d01600e000c9507440b0b1022100d142503a803890104020030b4590161805a000e41215001c1d03840850b10500d402201c1e0b03510544442031518402000c000f2403446800c1891000c3c0d040c0b13400710015041c010000c0450060500420040d245e200507a40b03000544d9a02a8005031203450b990340481e0a8081c1e062440300f10540c1d030060040c880802c0010303 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 457527850 1250 457526600 457526611
    0x207091508010608010b210c040f02120411100905030c09070507061401230108060915030708010c030c02070f05060d0227030f12090d060905060c07050607080106120b060903070905 79
    0x124039644032881442c6101503860410307c10340781c00001d03140c90585843c0e00701c0341c03041440074005810513540c1084102d80302010745d011100042d60b662030311f949041c014411210b603140d2341440e58445103000e012a8580f0200c080300341c460280da600040166008205546225130825000c200000c4455203131042c544082c007504880e4030400c1e4052701c1c0c810550080e02e4110606a582482d90345500040c0080300001800780744c2403c0e02203001800c9078030200b00d000001c00e1004000300d01500c032400040c00b00c80d10703000401c0071504400b81c184486904030b201c103021200c05484043d59503100540e1007000340200d4629203264154407103100703400720b0200e07c0c030b03800c0c1c050440c15540000c8134410a26520f000305803850480c40c1d024000300c14589041810708400501038003004c00d50f119142d076040e040c1001119007402c5d112010032200c0900c6420030020794081100c0c14480c02c035505140303002d4824842c0200030001940c59021080040d100c2c6415104500d00290403100e0480d11141a64082c190860b238 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 457529100 1250 457527850 457527859
    0x304050603072f0c151605070b0f1210060206040b0606070f0f030809070501320703050301080d0914103014010302010f050f04120804051e010207091508010608010b 72
    0x1007500c11841c224512510621405d2480c0740f40c40f51583c203108820740e00c5030381035559003e40c0b000059641c4001c1c00070300c111a20551101d507180c1d408410942e80d6800540524495042164103104860300000d04641140d0403940014165403042c0c00141c452051880040010106100710010041a42030054115120303465075012ba03a00c880c0307820343c0d4040310712a00780001c914080441c504180162480092040c41e108407801701d03268089403115074400c1d5400c50006d10000010000300000380007030282c2010500e40303035000318a483c2c03032403006102e00c4210522640300700d0030b2402c4850007518000450700ca40c001e0340b20040d01d01c0d00600703800350254261100d00341c2800403007140d0000c070150303035416a40d05171509800c81000ba001200e05070851800307a0290a020032000c40c0c0101d0025500d54400d1180010554440c2040c2c140160070440c000c0c400a0120888007269260b0b0300410b42405aa0200c800003445083c01050741c142900340340c1c0075544035403030300e14085001401904050704140d42500d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 457530350 1250 457529100 457529113
    0xb1b1e010b0306040519020d0b10060f02010605030331170c01020a0f23030d1e09020a0509070309020409061b0908100506060702060d060311010507050304050603072f 73
    0x40c240340e03c4400c200c03001001034004c080c4848080074880100d004c064005000d900a000c01959210341c030b41130541d0408400c0c25a03480070020030381d000c40b4800f0b80034000c0c4028440c49284c0408030b41d40380642a08081d0a8001001c14a009148a5862680d031101c070000004819903424040c000000807407a24503040c013070406400841d50001844140541e48070840011404481d240c046130181d5055500400b003608040f203503010b150410140180303040c0756030001007100400070f01c0a004842a20360614860071701d2414030159803030040c2e41c3c0880d081900e02c0e508607910307003404134000c28400100946c0a49099a820f0501c18039070f2000d00560113000b49540300944403a000d44652117980316090060340455288800716603681c00140c0c02000c00b81030b081c10120b140e40003812503040000800046650b40000b002444000c0d800381440850a08185150240701d45030030b03440e4411401380301d004003000070110380d01511410144059240300b01100c0c03882005c5c042842c8003060844042070750f41c8100e0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 457531600 1250 457530350 457530371
    0xa08010905130309050f121b091008030a120e100b04060603180f020a030f08030f010605041518050d0f1104020310090b010e090c04170c030303010b1b1e01 68
    0x15802800c2d20340e0152114a00035240c8820026041c80c01d04000350000d43c10214280d103c0420440f5a40e51040340c815141b80807110014030000c001c0007000055280000e8204101d01c05022048582d8901d1514001c8141c1503400744107000b803c002000c0c0e08291203041d0350200950180c2d8031108110300216000d102440e90b9140440540b01c12080c01c0c40c2024003203018000184c0b4182e101c0400070302c0134002d001a00e599842d8000101807080c0c0a1310300e0000002002030300003802940a0160038142003141c1403d0078401507403c40301d15401040d00340215070314000b005d00100c240c81c80091100410030803100a03030745015400c815807080200d038210318030038a410444c0b4050080e24441e844801000641074640411072020f413101d0403202c1e0500069111405c082e80340c40113498400c0c10401d8680e652503190410f0001a2034038040c1580194200240028103507a003c41141c1c1120f48008080d5100c007000c3c080c90a03000304041240050b8410100f5400c0c50041c00c00c130500111090310002c0107540040e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 457532850 1250 457531600 457531621
    0x111190519030f0c0f080708030f0604200c030408010f0c020706020a02090402040f0b10030c090b030610050c07241202031b0a02250314161206110a08010905 69
    0x1100008010520420340725400303a20a2403403180ca1800b807120300305c4003103094541000b00d9100c00d40a69200d44004104404030f400c196210340c1110080c0c07403c004041d90300103031101c142c01480b0301c0030342c42d00e000074600305800040050341e02400d003583c020852506401c1882c2c000f00034501008000d4001e0b60300018601d4004101041c50380c0c0c0280002d20260b4655081000030710f1500f42d40042607544102e0360405440d0241d00008001064400084a403031a200141a50000390b004240044040003040313115210611103c1024a060401680703941340400d40c2410500305800c0001c1000c0c81d54508203058886c0d00c6090380551143c0c480344100c2046060313903030607803000711850748221a40230410740c4007241140060a0301402071043d82c41c1d0070303c81c4503600c0c00160518002e000459559105100380a01d1005440c08907000d0300c01405041403030410a070384199688a00c545541c85001c40d00140495600403842011610004a503a411640f4010b406aa828020030484078a001e0004000713098 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 457534100 1250 457532850 457532893
    0xb1816090e090613030302040323010e0109030c020d02150c0303160305061021060e0108060a0507080a05060a0e0a050a151208030606040302030f03190e090c0901111905 74
    0x1205003c1c00c2540e64600e1200403500103500220200755003000000041061070100c030b1040066001078550802c3c8002049003035540c14049e45030240d1411403201d00081e00010007505903541611040c1d60700015000282c065521901c07440c000100025101b226044007100540c071a83d0750010081039520851412411504202d031159001071005106030305550085882c0304c0050000b0b1140210726189803c0700c0d0a851456005581028155006105819051040550007900c03150b0030071880c03030140c000412031f0300060300c1001d10b07d9030303400411005d031207030660400501140c0e0070181c468284422a20020300c002c903000724015240c9030f4002c0c40803c0c118810300444100241c0307184410a40d481e060b44a0340003424440d440344c410070000006840620400940c11800c201940d11000c030000400c440f0341403109002d0403c405005c4003402a80c6801549401240719110103407100030402c01611042135a0203583c034030380310303503002413200012503824503400d03902c101c0595005940164030003d4100 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 457535350 1250 457534100 457534111
    0x709030305090415090c050705060901110702090709030f1112060601141b07060302040e0a06080d031d0f01150801090812270604060513020d02040b1816090e 69
    0x20001c1054203280e1405401c000c849500245a1344007182c2e0f11002202100c0b5a05104404601d004c0358000512109000e000d60140c40800240124051004140150b10902c00700a00c502011702c0415034440c807881920018560088030f49080390218181506240c2108400c1ba12800d82c50006003071407075012840b2402520f060b110405150140d82e0383d840a40c01001e00c071141c064003844002d82c100c104100c5400140800e03100107075200d007010301c110090b86000f03001512540c10b141d400c20031030030002200e182c0c0c24018540094080203038050f40c84404192407a0025038403815551103145401984880180703540a842441c05075a0340030201e00fa01c08081c400350680c8818440e9440501034840034075404050002c2c80d86400c0e40903014807204c40103005403c2159408a02007008124144c880c01c4c5e085001d18a203200c0310100c5900098002420703540c004d000e00e84a08141405482d0740720954031a000d40300c00d0000b6480d1140c1c4589016420031650000284c0c81c01000904100015040b0700a1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 457536600 1250 457535350 457535357
    0x90a050f150904230a1b0906030b040207020402030a06050906040920030304120305041a1c1a0a0305010b1507020a030f020a03060c030902030f12040302090402030703050f0a050607090303 82
    0x603000840c81041030b00485005a0402e0f101e88510060402144024222101d1a42100d21600b4421900380448924200004907101d42501d000e5032250003240001c2152558500401c00114480c003040290281240c0203420900200501c81990001e400c190700303880c415244c805061351100f04001c113803840e40c000a000c1d40c514445090b414412560394030700740c240240840e45004d580e0880c03010748884d03541003070b80000c101080600c0854403000d03880e81c0c00d1030007550b85800c064042c3c1c82551f8048604188214403079a42d111134001407180100c98140c1c1c0c00003001c080d26142d680c14010b0180c444040500d10034446c8e400340c1e4914480c20019140c6907034019100110b46c0c0d043d942c40d40c45019881c84142d80c4610251800000a24140a900f601110590300400c9500203403050501d0080b503a007022400d900620000001203007031178150f0b001c80e901141c10307118646860002c80d04200d2280c00c00303003940c041d070b114400d0703e404005071001c0c1c10f80c402e00840b595039440e020221294186400004d001 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 457537850 1250 457536600 457536619
    0x4080a020c10140315150304050705060418020d060b040f141816050903070f140306010b090103090206040e09010603151a040506010e03010e2103060307120c09050408090a050f 77
    0x400f407000d00034580c0600da20b18001403014540000580f01c107034000c441644900d00000304410407105002520080506540084c00c1609090900002840f50721590801c503601090900c001109034018000074246000b00c5035845480e0322962003601e096000d140b20f1000d01501c03150b124140780000340031809078445c41184a40300d1413050030308000701d02c3c1c100040080601140406950500403040240f91610010000b81d00c0d01c80b4540c40d00540111181c403e4006d8401080450035030b808441e8103c00034030303001508032a141300060440c091504461400f4814400b000f14400301580000d0641c4c2c090100881d400c003000780c100c020384403844902c100402100c80300c840c8500380340c1c000c0b6400107414103140c201c07003042e0000700c0e08480074201c0c01e4010754441c4100031201702c144060a0214010300d580140f8529052010a40d0703064188100304524501402c08000d100000c1c1161014140c4241d00307001031b0815051013800b43d04400c02d40c510801c243d02c9d00081a107807140301e4803041d14014011922 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 457539100 1250 457537850 457537877
    0xf030f1b0f020d0c1e0311012c1305040606060206010807060903061d030c060f0711150901060e07030e07060504080604031409060c0609060f0403050304080703090e04080a020c10 78
    0x80b840300000f0211103401c2c407118045600c44400081407103100300760981481281c43c50914040e03a43d800318409051000c002e0a4450183d10020a032040701d0551000300c1d010410300011812403072400d5504071001e4604007c0c0300c00c10030640c010744104d070000d60850b011750341c81c1c2d564176490b5106440303804007007418100208002130240e04100e14042400740020711851003034158604550040710001003a400c14000c012400c516441010b40003506491f00100b100b215801107641d440301c004150301c551600c000011040e4200350070140c09418034980c1e001030750800d1000540500703081c0aa0041d1801081000f1440c248a035080e80c0c12103840d1340042410b92119141a207180703001e000c50031000b2804100140300c0d038803100300402802007210001c080510b0300005250034180050540c41e1903000510a21011940c440f05881d08160803080c40c40d075810301342c502500c0d02c0007254012000e1a01038001c1009000100c0c01422181c003694003070310041d80111040022000390b5450000104004c52101c0340c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 457540350 1250 457539100 457539109
    0xc030601030b0901020403170a03061e060302180307080d0923010c1a070906030605030c03120d020d050106171501021b060d050c1c0207031d030a0f030f1b0f02 70
    0x68100e0f5803200014685070b06d03a10ba2071059810300b40102d000b0300c000100528071503858481c1c18001c001e41c10140704905403c070814608550180305041c2099000b00c1d04401fa40e000c3e000000b5000e00080403500c110b075036107041d25110707007010b40404040384080c040050b41a070446000c0003000c052850b072011015945c070055522451806040d80c008404601c085804041d0700e54160107810b060f240d680e40e55160000c002c00744e880780d4011500a030040c0d40581c4240d200003584c0185034415004035500d80000d050100c000340111240d44480b50305000002510a4008a80c05039090110b100042503542381e02400d0654480c450005005034816032200e03060100c00e40d0111000d40b0014045443d0002d640045001ea4005840130807411500107035901a01c0d40e0180d61540d04007103100e0039414240c490304c000d010f0f0014800074180480ca6050b828019075000c0c0a144030300d40e0721007c010709010b241d05008208415840e04e800101e044000d010340450201440c461000d40d1100400900355515400e20 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 457541600 1250 457540350 457540373
    0x304150c0507080619090206041401110109060f0c0c0506160201090b010b030702011413060203130b190c030b0d06020a020102121806010f030b06210a11040c020c03060103 75
    0x150100961810305000169090110800500490000340b0329810407004440d6640c200580e03580300f06107401c400c0c80c010784503d002e0318100d0f02c84c05a0000811240d400584a0212013504400307035500c0c2480000400030183e00502181c00a82ca0820005ca104402928001e01c0910050300f5584503400040030004040e0181b030918850384004242c560441d651a081c03100c0a0300001d00c140d6010042180082e424800c40703106001c1c02c500402230b400c000c02c03c61191400c5a030040e11719500000007804600300e210f241c1c070b011644003001015600d00151110400020591441c19503030612543c0c0714094421300440b484807000603d0500035540d00e50340c40700207511641d10b04d000e55400b440104044180c403002188107240034000b102c1411852072003641000d0050f04610702a0401031014804034801501c8581c1c081c0e015030340c0da04a44418054207482c103403101c144c000c1f28810005410300b001100c0b521444258419030f0207102511038000107988940c40c50217841e4041d07100d0b00040000c510500c100 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 457542850 1250 457541600 457541639
    0x907050901120f1b24030c080114030a1a0a0b090c0909040f140a03020f12031810020301090b1306080a020d032303040b18120708040b030405060f010602010209030304 73
    0x900d99119849089215a0450b03010081d0f0ba0085c0c01c40519861007440420085015880c0c2000303000074461002d440420306000b0100105080500251a40c804105011599800a01040013003442c054080444401119051841810700120399814106961702500035694840100c0c10700712003030b0a205544c10020300c161214004a8012400700c1ca8900f40149845c4442000d020701203041d0401078070784003070403078100020340c000c00d00815aa0b0498040d01c0d0044403104494204203048540c4514081c5107807150b00c0039501c00000018070301030b2070f88546000d0b2406c0c0c07080002e00e9075610b01242101c40794410046541c2081c62400014138004080b026100d109061192680041c00b006d801c5642c0e01c0400550f030280c0000a0009000304400c4603981300c1511a1000d41161545a480340c03586014114884400e4000c140c400400440c0c005540c044c00c062980d0a8483c0307000c1c10040e6440005a800b500c500c0c60080012036071038418021030b25030f450b000d00107525052030711503030b081455500c821 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 457544100 1250 457542850 457542863
    0x607030c2a03200712050f060a0617011803180f090506120a020a0b031503011104030314070804050f04020415020a02010207050a030209010e060f0a0e0907050901120f 73
    0x25030724540c00781c100d000d8a64520300003800910380186405441d414014910b210f5800800702c00c00b14030480014580b0590300d146001c8030882c505407030030b149080c00440100300075000c0d1100300b00f151545a03014030b003280c40a0f034502c84c841c038103140b8041c22600d801b0001c00300307102c040d80401d000c06d01414032408200400401c01510b07c0e500d046214030340c0e61310307048010700c40d44502c181305091a003244121080003003103000e050079004950005202c10090300c1102070458010000450034244d6403454426011b01a00134841060000c6000070030b507006000440120310940706d80500041e5400a03164116804808245042e0a15040203040d444102035954855001c100c0840d088110880030403d6041c0358000300842a07007840064142001c81d0007031809420652002c05c00b5941e02c48529044416040580710680c6911000c101c8849154801c0e6800c032040c40c00024903e81d4580707003140706000c0c02d400d9490940c0c64030b0800134040f1081c4140c405180300440e484000c61406106003041e98400d44c1c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 457545350 1250 457544100 457544117
    0x1309230304050910030b07030228020a0b07090f080a050f060106081306060518060f010503070f080a091b080609010506010e0f031615080603010e19030e03011401150e030607030c 78
    0x50b0381250700401100c1104c0009d80214080c419200d14001c8102103110901195101c40c43c0e02c90002d40d034920400c00981002512000304001d503000340f1184028104040c400c07083c1a40310606186e45801c6420100c0305480343c03812030b1404810100f001d6060f61a02e6407507244640390318100803036011007154265011070352003400146036540d4110f03002c4802294660510786103010020004110800c174152030522000304100300c030304c90f44019138414406407810804926120301100740000c02c0040801003142c1150000001001001d0101350308aa00c20021114035070381d4a0712036402da54050b00d0050120b44407400c0d558080c90884d14800c0e418101800f250183ca00102c945030002070154800103840302d5144104122a61050010790300c540c00360300034406000880700ba0741c2e5640b6020101948102083d44050270944510f0f1141c140010040003409200c8126a2202d0007207000e01c103444641a00320700c040300030b9019462800f0b070002d00401074240350352440c0050f0301420402440404000a00 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 457546600 1250 457545350 457545353
    0x10501080f0606180f040326011d040b0c0c120d0e0d090f05060f130b0903101103040609020d0b0403020c010e0d050717070906030507210c06051602130923030405091003 74
    0x2007807411480b00b2088c032045c155407400008443c91092102e54040d400500000c0002082c02103c02c1c40c0c0040220340e40c15582c546440346541000305141c60721a0314072000456900c4d540c5d054000c060b0b4076040100381c841c0c0031441038090720740c034000e44543c403448500d10004000614180c000b40900ca030142400320f1902444041215403040650407504a60a0108038842281410000c0c10303440303101502d040041d07032400c0031036800a000c0280001c1881e0b03100d9040b1000c64a402d60110b01c3e1035400301245480e4140342c0390194640300160300090001c0d1030200410007524040c00041401d44d040000781508a05160b8012450500f058000d0b00c9071290340d00009100700da5100e800d004502640107449294100215002401007100c9503251b641040d90742c00c0301182400720b6110403140d550806696921101d0024190700c0380210020f940030340389205000300c07024540c01943c210341c40b60b22105050607001d4414414059454005c2804d079100340002d0209050002c002a04a000c040c51050ba0b40d07034030b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 457547850 1250 457546600 457546637
    0x2203110105070c0b0703020f0306101103070303023015121617030c0318041806050601030501150512090a0c06091503060b0d0f0e010501080f0606180f0403 68
    0x2030320800006103107110f012007880100c61000e9000581d9203825442d0800c2982c0103a102e00001d00881d104171070300c052403090b550050048201414481e02526100c1c2c406043c007034025080908038001042d05c2e40c1034840426410250f016400c070719602d0004a80e26646030810105803640c0c505500440c0e1070f100b0b941c002d07400300f108100800150900c210355a04004c0d10282c45000381c82c4d0200790350b1060101d030012540100c1500c00204d150003080c5040724441000602900071581840d00011a03070f66600140206600078500c24002030b241440280da80724a00058945c00f068100c3c0050814481d106101a0020406410840700411100c42c070041307840d642070784c01c000da0040c0041041407d041080c0d26500300046041c40341410308000303181c0307001c81d2000144928450441441c3d42c1d841000c216100039441300c0c0c903c0324100001c110545c5c4848100f40d41c0d200050709060382d8031402000903550b29082002c03d1145108402000268483c4442c2425000028101300d0901c10340f02a54460000d0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 457549100 1250 457547850 457547861
    0xa0605060f070c0504060605041e23180f06210d200a0302060a0b010c0f05010b1903020a05240a0801050a080a1a100b0301080d03050603030322031101 66
    0x1210710065520901e80c80c040103215907071340c40300b030045007400c0040200c1d581180640f02240c2c47c10381e07030f941180202a03031404891202d400441040d0b00440600134a02d426140c0d00090071800d079008819803450750310b08420407100700d50002d042050701001450500b446002d5501c01c0300c903440c4a900751a003000105052401c461400c00010317012041c1420180c1451404031003071155100501086840303920000d4884000a0540140c10307100d1310b010790720381d1049510030380c0c15401c030b030f01800710701841d11706940a401d4558076a44104070320140103551071031803c110400c0700d5004054420312490201400403000a81c00c00c2004045c01d00d0011000c1c40114001b81206043c40d51041d51a6040204010100d5119040814654002011240001c41d96200c0c03580c2804040da440010740d941c40c2960340744001700e4110b14003652000c00001003004000891101480c03031a2000d00c03581c7e507114107165882c0000c032490464203041c040358040000e0007075001501940603140502580e04081061030035140c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 457550350 1250 457549100 457549117
    0x100203090d06020c0c0d110d0f020907030c1805060d05041b08060907060c030206180c180a0506011b03030b04150303020f010b0103201614032508040e0a060506 70
    0x1500013034100d9008000b440003440138a000c9410361071214454403582e16190210300d54900854075a0b40d00000e01524610f12241507600810013011850000b030010302904005e03070b5010200301d0801c4007403007440c1d42c10384100594501801250070264801e200c840500409042070300c0301e018010982c2c03081000c500540014091643c01042c1a080c10418507203032050079132004080000e02881100041d902040c40d54000c00600c4c40c092400001814240c203080708440d00c16404440210000407000100d03250130700c109803001c820403071aa90100151440510380d1416401c2c1500424481c0000380a036201d10101c04019100040c1c20164510400a01d0340076002600948d102c184144012b4109000b0745940305420310b1705014500800300500351070054540d40300d80f0b5910100366988114102c1c81320455841c6c20484440c51031540b07a50450b00c940c0701032170f50040c12011180100080341660000201d060340300d4030161030a4907000405206950140c0000404c075150400000d032030b41c50201414122 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 457551600 1250 457550350 457550363
    0x706060f15111504120201140a0c02070f030201051209030910170a060b16020f0303030103030f08090d080a1d0a0507090608010e03160317130c090b0a05100203090d 72
    0x1181e011806000c48091000c03000702070f48a5080d800201280038002c641080d07200007186480086010309034050854000780c5040107400c0c030100f140d2400c0c0d60b0800d00380c070010742c0c00340c40040e0307200d040c1c403171040940d4003003c3d000c03820070030010754a006145003103130b0300888030010b032402d0103030450000d81300b038260f0f000341400124410703901c908941d080b6121072b4200c00014000c001d114600f0304064071078000d450111201c940203403040402d41d1a080350300350711035000400340e0307980b581c4918001d010290251500b50004004c280041c00180001801f04498580b944440c100e0b0307901c802c8100040c1c01c40240c080a0718080b038241c0d161919003040820000340c4110003402045013028901d4040714540c0c0d015480603030404444c1282d5a0b004412504028180080500318120b60b0909445030300050b50340b0201000414100454400c0f03010540100c54401c82842500c299190040006c0c1c4001c413074003a522900c01c00d0101b10340d01e01104403c88071206070042c0d034280900000020038013100a04143c2c0c01 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 457552850 1250 457551600 457551629
    0xc0b09010516030b0112020a030603081c050705070c030b06061b0d021b0a140103140115140702032508010618060503030c06010b0d18050d030515010c02060706060f 72
    0xe0040c0002c2e20380e902c8100d14007000700b007031048002801020303449455060141e00281e80f041e1540310741c000101a64000d005207664403a08032004103c05200e18511170b9075442c00000c6413200344554116803030350760040840b40e40381c3d04517202c00d100e41c48080e00301580000308110703285010385480c0c00581c2d2000b8072000f600c920602054003078103000f031b003003aa071154540b00032040c6c040c0d83d900080103080c1e841032032585000700c1d0741c00700603402015220050311a80040308000124112809100180a0179a940b0003c9501c10010800d0035409040702c025456008888408441e5010300003a9000c50200c003a01000e00d030b5640c1c40d890844109400c03030f0782d13000115000c40d0082c16a81c01900d0042c0020381c000e41c072b03044a0201e600c0c1c0b00c2106020f20242c0c0280019201c8036845036800c80c400c11200c070650300681c09400d1501c3d50362240b011880101190400e03000a218a0441004100f0f02006031a80003031040307164208001c6a1298808440140c1e482c0d80104040e200d44070b00c50090070390002003042 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 457553956 1106 457552850 457552861
    0x203070b0604150e0714040e04030507051e0703020f060a090501050a052206180303080a0c05160b0106110d0504230904081b030f0a08070c0b090105 65
    0x801001c0560f000c5103052003030b000341c2e010f00f119464160745080c688280040500842c40b4164072a03840740c0024002c68040e1006180d464801c90544198400980c017079140b040da039400202490b44060300a00441c1410007031546480d8007140c405003040000c107401400440c95004850410102140c600c4020b40201e0130f440709564922551004200c0c0040d0380000740700740b8490b140002d0340340760716509040031400e003c000782c907056568982c840d40c40c41c16079805080a84440720400404110143c04000360382103c0c08414440c11001e0242c2d40340800052401044d5400c10a05070403076240074101c03a40000440e001c40c1c00c0031500c3c00d606c0704100390350590312540c3e40000b90400001000c200070040359200500382007066103240300350178900010031980c0c0d0068050210944a0420040002c1806040c0d0303031b50f0003101c0e407402c02c080e41290350311070801c00700035034500e89944c3d152818007c = true := by decide +kernel

theorem cover : BRFrame.Cov 457374100 457553956 := by
  have h0 := BRFrame.cov_init 457374100
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457374100 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 457374100 ≤ n) (h2 : n < 457553956) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
