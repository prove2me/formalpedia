-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4665
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:20:50.15869+00:00
-- url     : https://prove2.me/submissions/1a672a1b-12c1-46bd-aae4-0db48e19d228

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 838848920 ≤ n < 839028776 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 838850170 1250 838848920 838848973
    0x60c080306060f160b0105030c060c0d03110913050a2703050723060a06171b0a050301020406120c02120a050d111617090d0201260408030403030b0102 66
    0x4440d03032079080307078600055403040030340d541130300f1301c410a00c1001e02034134501e02810ba038021002e44a04440320720030051a406014285401c07a04400705801045019500240c550102c255401c1e0400c0c60000015500711984408258010380311750800183c05124440e0094080c151402103103203541d0309800d1120311150500040c1401400104135051050a001c86904513900c246c80c1070408d1034000320741f07480b0344054071418909405c150740403035500c2c20004c0090007680c0c0c0ca030041190780c0c5070f41102c000d607034050f44030590040002c03400803c01361030070300052000d8500d51315044501d115135541c2200325242030b8108000c5401031031120f0342c494401d00845145002602d400b58859a020000400401c80001c203103200e85000222860038180140144500500174048405290720080d8030a041e07224000400d0351010740d0744031a90056000d044036800030206d0245041c02c0304d441541086500b5030a4506071056900801000105581070041da240343d0300c01e2010b8403c02c001e07040c0107444000600035 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 838851420 1250 838850170 838850179
    0x9010210200d0e01021323010819090c0b0417070501080f1503150a061d0703020a051e040911090a032613060801080f1c030617010c09060c080306 64
    0x50030814072510343c000c0d0144181c0d14000b10350701c1290000840100955125000000c0d4000600e4145000c41032000400740f90182c459404581e07628582c04000300700c11514250040d5100064008079551105600140c008038540540d07aa04100211480c3d11983e1924101503020308410312240c0d0740140c3c043e030400c08112000d6860f0300c4908580b41d8a5200107204e0380c0501c20409160030780c452440900b0701808500004000d440d07116009040300d00390a864941c251240701000c20b18081c80782d4001d1910801d94036040d03041490380026540044021809204103c0d00810305203c2e03541d03144140102e100e0024801440c08118001081032490305200c090042025004040a000c07107401d1005180d6543d18180c90780c845500707004900074821f0b4081c020000344d504002140444001960065140c4548000d08481d000d183e10524180e20084e0500301305a22034000154000003a0103003140041700000105040740090801000c44406a0045003045920400c200108202030102c170f0300854140e5 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 838852670 1250 838851420 838851427
    0x6070801050604031a06010e0d0606060e06131406220807090b1f02010204090f020705060c032202011704051c050901210b0d0f050708120d090212060a020901021020 72
    0x1b0050313402d000362161258000c4100c5559004100050f448901911415100c074000d8052120074040c26008290084a42280e40c1c201030001c95030382403805003100001080d081c5030504900010f41181c1c000281c0310009002c50318140080700d814851440a0100c42004001003001180094803c2c04a0900812614402252445550300c02e40441d0054221000c0503c00010f45403405270080d031000000391164010714010901c40240c1008980c042d0031903021403070314155440301c59078010b01d1410049050040007001c14807501905598a4400e030701900260100314284860000c100002401200401c2000c00a504950f030304003580160b0301c1c0411490b4420460a00d9030f00c80144010345205900c104542c40b0387e030400940640c039601031440340003629010741e03540d600e0680d650007840c01088501401d000e00a01c0c80400d5114100081c001426180e131070340011001030030f003e400ea848405003038000590710403a580400041c1030402c440e450400580e06002c005031035007061540c07000240f00e03000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 838853920 1250 838852670 838852681
    0x140306011701171011091905100503040b06010c0b010603090804050d080c2119122405060f07110d060c0c020a0e06030601170a0503070506070801050604031a 69
    0x50407986106038000031081440c0d6101d40205054000c211000d00c40c0c0d10a1001245101032180914503558021010141c144803118003004031480c401c201010301040c40910000d13040e510704405c9141001c260b1a140d517203041130b0504510301c4200400c01814880540c1c12034000a1003104458112200e40c58006800c40759898224281c0c861070707014a0740316041d01180000d04c56490020040302607800212290710000501c0b6200c000041101000030660900c05480c81d030551404103807412495107003240c020a05040b1100403101031002403c00d2454550b0240c204c00040d540701c0d0080e00c81183d641303090075585003444c641ca1007820402403039655104000d000c6920389600003001da59000301c00303000c1480390000c01002800c4400c811b920035140110000741d413400d44880c0e00d000c0c0b1005005011660b08010060700000c1d140c0e060440349103d420615408288144041e158152042000c2c204501701000010f2500e1010380149124400400c800c00000e0780c800035038540500c1c01180c0711296900d0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 838855170 1250 838853920 838853927
    0xc0618030203070b0409050709062312040303090b1003150c17010b0a09050904110405090c150316022b0923100201020a0912020d080703050309100b0114030601 70
    0x2688029010710400002144180402c4e015006649000e241080035a803020000c50b80a0143c1c8660030105074103c01c199000b4854030a54886202c08001701c629207100021309081c1c1e40b0040b03e0603400079035a000c404042080106001d0340044440010004103404c680390452803d0250b0304030003c241c0d8030041091403a0251541c0340c1301c15100034003001c242d80d4886000465602a8022800084d40d8134800f14161504619060103660051070716010341550009000040030003400c010460301c039010030b001051703665090a60400040098445e1070303040030040e444112548520080c00c0d50085400705900c080e01e81c01c02c0030104000d82b1031030004101403905640c0d610f12600705100a03441c2410f104100c0100b030400c0850134009440341c580781d15044404078200d00420400c0130001d801d00c08104580306280c142942c039580000c00c2d0141c0416240da840c990b9500400040340400c1c2c0120801000d610107105d10f494602d1070050611910700d82d0313000200b58035841d184ae4070a10f0408808585564031 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 838856420 1250 838855170 838855217
    0xc090602120c070509010b030709151e0306170c0a09050606250501020d1b09152a120f0e06030703050c090918071e1224090b010504090c06 61
    0x4c0640100070750750719000000f03415401260280d0110b9804600092400402d11000550101c00d40d1201200a0b25030401d41e40515421005020141c54000120341755a0350b0714003040f80021840201503420034071044c00018607096011420440c03401f0100101515120226110f07900c41c80c1e20340310b14420800f915000100d25a001400940c030100d002c03e80d00c6896400030a58140341f004a02c000300b0245403c94804d10745014500c440244d80700300520300c0380190200d201440c0c4504c950b0b002c5041d00e00b1071450b0b80c052110107952904800742c4070f461158000310405041d00d00780c500a4041b0401d0000300d1071520010782014200f560b10306c00101880700c01419184060401400c03001c050625481c209601c02440c10341e0103590040240010b1001220031f06a1140e000e1070400040d03203071400501c42418410500c0c2690307031010711031340102054042c80e2000c000c042680c0d00051440c949003880c11100c0c0058010354056031030559003a0214443d1407a540803100305180942c1c400e01a40c0a07410003c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 838857670 1250 838856420 838856429
    0x60f0c07181a06090f060a030905100903180609050108130f050609010513020108130f0b0708161b23030d051e06150a2a02040c090602120c07 62
    0x18080c0741c0722030a207606401101c401030351581505100008902045014410522442d90200a190840c0f41504001018141d00007a81c180000d03c0c1d0800e0f01e40d2030514580b403114640d40c56565900208051b007100d5283d003800d0b00041e042e040a0300b01580a00040b88601415061113005070019080044081001d516240c0c009184034645446103044ae680e0001910600095400c080000c0d00903459031002403140e0742c050756440e41c69142e00b003046e00901c0342c00c03009840c04e4401c1c0750b862000c01d1182c514580140090750f680d003010301e4842141e00a200c10502301004100c000001c0409107105082d80320f481c107402001c0030400da4000e010034400f40342001c640d503900e8000815002071056480c0d0041e80308402841030540000c00100182c0c3c00050100c0b0364646c80501c03010b018030415800800307002201500e003030100c2072144c108820040c0149041020b513101e041c050180302182060300130700000c120b007420040c11090074601c1c0652264000b0659007408400460311030b0286900b00718850051 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 838858920 1250 838857670 838857689
    0x1008040830010501260915070512010506030c0403080a0306090612061401051809010f06090605031603031b1506060e19030f02040209010210060f1d06060f0c07 70
    0x260044081d029480741c20901c810300012401d00001125401a85d641c40e00d02a241d4460b08845580e040c1c061100e480940800e440744162210139004000c4845007030302415542c0c44058075071a0981c00303d00c003410141c04c034a0058806005009080543e00f0a80b0141c0380d00600305a281c948a2104800511a0754003c40c022801d0031000245124480b680c5040c1502541050003141c2002030f04d4842c501d001e100d055003010500d01d40d141d0040c800200240c00442080001c200d401c038101c1d90303d05807a40340e00704d120f540d40e032007004000c645010800e04413036100042d070130b0110f1807860310041c0c9410a00c00405182440c803100710350422011104440d070700310030800704000d0507440b4000107000105c900c01c804e000b1160703090b010f40c03c841090742140403260300510810301e4a84036800d000c065004124041e065100350580c0d1800c1100074095040504201d5650300c11303a9103400f5003542000d841136412040b000401051002540314901100c1d03464200b035036078507964410740c020146440390303170352100560 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 838860170 1250 838858920 838858957
    0xa05030414031827040b0106030b0111030f2104150609140601140408070305031206061801120225033e031908060f2b081902151510080408 61
    0x1b0482c1880606040c0c4805035401c100039083c03500199102c903045003c0b060350b944180300e0284d47c1440c1400402140494007410001c11084420304100e55805441c2260f070020404480d81600c0441d215030002480c0c0510300780466542c4010b40020924050b0803a0304115070048802c0c038907103541e000c903001441031000f1030b80815902d040207074881e000300444041c03442c840408030303c4a16012065803152210100c0c080580c081c510300548030b600c5000b65004046400b84901c86d400701d0a9240001c070940c62071007000b064401440c00a00504204862500e090790344034042c5078498192841c00c0c0500c0c5424807010001c16900d52a07461405405043e9910740c10b000300c0842450303402a101c5001792402d8900003e400500000c111004000030030301001076904101d60044030b001c00702c120700e055008201d41c03490003c80300341c0818030740b25507060407025901010b94010284844d500c07269011503040b00803045100610001011203014041240c20001d0f00d801180500c00075604540074620301c2c1400440 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 838861420 1250 838860170 838860173
    0x8163c0203040503010c02030415030203090c040e01050406060f0f0302040209030a0507060f0e0d08030a020a03090203030d0b18060d1217070f02061602121e0a0503041403182704 78
    0x15294064060f0500075403c140d17050400301e000200782e4056489a252200c03000c0c075a8207080707000b0b420040c425015032040c071005060a07191482200c1d607150b4140001324103403405080040980f41680e01c1110241900321013005209242721100b01507940c11a0056a540d444500213032034484c06003800b0740075020b20744c00020102e03081020a510004261034100064101c802080021008000040e1106004200113007484806500038460040c1c0c40c200003c40a00e0750300440d1031904481d0b2003001661340e6081c142c0d600e2400419140310521850161a0b10346042c1e00400c03000c0c005c4403c010f2000d5206011004050f00400451407006e609058054903442c10200c018018170244694070050700801c404207600d00c00e1304c210200000c01075002041c5860901c0721a00055001c401d048900922203e0144103820301c15006044000c130a59902d61682880d0400400010b40780900c24800d50040261040c11544240122201c0000304c61a0180ba50b10090344001122107084024528540e1000c220 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 838862670 1250 838861420 838861423
    0xe1008100e12031003140c06031618090f200d020a091a040e090307170901090806010b0306040c0f02150c090301050403080a0b03070e0109020a18080d08163c02 70
    0x3c0403a401a486c1017450080700342d50319164654601400c1e040541000060703031000b01c65200c08031001d003c3c60701c1c080414810595800d00b4883d508020246034582e0324414103c6640d010b00403640d07410701c120102e8080d030041040708503c5136503806c1c21241d8012a41b14201c0d4018909500100607a00c451070420140810415241d030040c000d1041c0c180301a0041080000000261468560f00141c1c1d103c00340b10300d56000c003058210805507030410402c0d13080403407040c2040c0030060090920020322516402e200c1d04210680b14a58180e070100310034a00e14444095000448489500448407202d500d9200c04c1d41c1c2c1c0681c1d2050044182c0c2660070041030104240e404118103106510080e8100300790005141055250080c900c520400c811f45000140a0508107500400f88040079007007940107015154840700740c4076110b510403103054102114900c540c3d078000f40c4155000500b14035154201c101d03103602900140781e04808000c0c0e25001403c20b0b030561a5070598907600710206045a541808200d0001d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 838863920 1250 838862670 838862701
    0x50304090c0801140303030f061309052b0f1206030606030b0f0a061409130209040507030c0605030c07030e12030d0e0f01060828080a090e1008100e1203 67
    0x10000b070300c1a0000261030b400d85030442841c1e14010702962464541d00340701031a81d1405004240e01000c0014603402c010701c54400c18080c584141c0140005141d1519500c100742d0f0810b41c0707066060a410802c0b114154000340c95208c80d0503a00300700c24510408024500141140c0e0402010306140070000301c14003a03040c1406225515441020070b45548400d096806c0d1134240c071407031801010380c1c140005903103000c513001903011001e91400c108a040d90b4000407041502914291002e40000d4401d2050010b00310b5091b001d890f0909259180d400e008600c10068490581c3c042c1c10004642580000c41e55021120000c0d20000d204480e1a2080d070000c401c0240102d01d020082c91080c02c2c208080d031801070140da0100d82c0700c0d2000e480c1c10301001a80052004c1c500241e03410841a441c03011000400c00400760041031260340d51041c00324105080b600b004c80014100503a03805808004001a4200045074000701c0d005403404507100b064003d40c1860148004d5403500c11210203c1000044841d8150b031 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 838865170 1250 838863920 838863941
    0x62503020f151906030308060402090105070f080408060c0a02281a07020c0a12060b0d051005040b0702061306020f09030f21032a0f0703020c01110c220905030409 71
    0xd940d03e814030708440411503416100040c04111fa40300001c2c1680f406a01800c08400c040c101140b814030f00da51400b40c0720003802e82c12183d03c1400f04090004040412132503078042081130030b00e480d0181d41c02010355079404280080141401c0843c58011207003510704003c03c1140c0c84602c03038100d151098007142c60b007841101d031040107108504840c2820b2400710200c0c0101c481a14803074925000d141c4810000e007441d0410940c0049051960b54000741c0104a000711620781e01c100003c8508161402400c04000a400d08045600c4041401054950400120740c0150302040040e580c44142d0a90b010030f000302880b082e49402280700081400102141c10300958102154004c05903000481a0780355000a4602c0186010340c00302418800c50180115103251070244c011608000b4451000540740d800b9010031401a0061500c8038559600540c4007440b00c2c0b51000a03141c003040300804a240c0c40c00c00c00d010342c0640302c0728078030a840c0d000030b0b03000311411a0090142e0355900d480e641410007800c085100b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 838866420 1250 838865170 838865191
    0x51005070519020f01090b030c070615080706180602031204210816031119020118060b0907050c0a0602090a080d0216150923040524062503020f15 64
    0x2840c070001d46c82120b00e40281e90364414002e00b180c43d0303442000c9480e00310880444075260b0b40c039030072602c52041040c0755008002150040885070304020004168180d150001424520b11243c20300c4455004000d40d90b403507500030440300c070300d039164201410a1000030000303101f00b090000c40030000319801a1030758802c403400b0b450040a0143e42500f00d04840030b1040303048640b0b4060050100710340005884c2914102140700204d00c0712100884241220b020311012a603055031014582014103220340d08a510031514141513080c6920300c11301239226584840c000b8041580003070342c1091640da104852020b00382035403c46612900c0d1501c013030350301c200d030752006940c5c0340e107011000031b4411001240080c5514a0303564801060b240954143e43c20606018403000911101c030301604503251407141500c01c616161425000000d51800465410b810245081c000c10003008101000010308004002034401c01a0000945040d81000c80c2400b245010b804494021007580010030100403070864068a505207 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 838867670 1250 838866420 838866439
    0x111905010315030b011701150b07050c01030603020609040207081603030207140d020c1201330807030209040f1a04050a0b090c280503070b04030c0b1305100507051902 73
    0x302007101c01c299101c004d00703009000d001401302d01460281110041e000c00d0002c174500301400b03e20b0440c2c0742c0d40d4202c41001c400100780c071000e2180070171040c1c4000310f00b82002c00c20316080d40c0100d54144a12804540a40c0d000079500e0100041c4100326030780181141d464080300c0046140040295010810588031400c44003220620158085101034442005400814041d8000b81c00e02000d0489110095410755840e000d031030250402117901d14140014680302032509054070600341c07005030540c014401a902c4880207000507161580f0058209403c040705252070740b042d00d4251240404032461302280b1a12009010810200107000d4252038440c0301038101554030698081e58940e40f00381c446920164103500300e0301d1541d04402000711200640320f0b43c007903c0d40701c2012901d0300d4a80c0c0d10418220b540007034200140400d40d00c501c005050b5910b0310501d0607a81c803241c40090209070007564824007044c40580070b1140150201c2d034010364041300f51407003070724013903e054201c00d003d520a078060090342 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 838868920 1250 838867670 838867691
    0x1207120b0105091909020d120f0f0219231209030c040513030e150403080711030102130603020d06330e100318050312091020071119050103 61
    0x580245100303410040b5044d6101d00d01000361005080d40860503a008a8070080300e50108080c110100c101b00156150300c80340015101c00244a01c0b090701c04101103422841790401c1d000002ca4011480c40c2e0802c44100440513081020780381902e080034603061500c43d20130301c0c10070510850042c244850007101074484511080b02400709603101100c2c0313085c07500300300001c2500203405200c0802c2612800f800c0d882802d5050714180c1140e41c80364000b80c4510101040a03020006813441c06681501c081c2c0095081450094101441000714028a814035802040034440c2090b40d0b88018020705d40001d900911010106c040716074408890311035000000400312040d19180584074048007200054000d000e42c00003228100c00408144a48440341100441c56401207001000603044450380282000c981c0d0901d208a1480c06030161081e50700303103061842d5595489131001070349910022448049035a801107140040001d54074028541c2c0c480b0240c0e1070031103460040e900400507903100380c0f010000c0000c00c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 838870170 1250 838868920 838868929
    0x15020a110a0e0112050106030209150301050123010f2109050f01060501050f090d05150f13020a06050d09061a04151a07022716050c060601030b1207120b0105 69
    0x1400740000b0142c548004104a0440e0701d807401c4218041c900000d141e5460781c2c0040c40340c80d800c2c0c0d22040080304119141140745030078801ca900401e548411545030004c0894026200300105005038107101e003115960311100d001c0c103090070b08031804102c226813000b0081401c200601c4000001d562500c140c480c86400894140f046e8070666905844843c208001e004400600303031301041c1070940045170010741c030000403800c201310149414400454002480c0c8061000e0724814001c146000750803070320700c04101580380c000305c06040e103186150840c3d4a003040b208101c050080c0070401029180303000001c140090958411842c91380d411070f0140910212000e903000d0614885c0500504003030018003080c82d4a075684000c1408910240007604448864400c0302610016403c0402c0304000141c00c106003028910700642d2411480d0400c94184010b00c0103da40d1404018481340c103065980c00005131036561550b00c6141858403c084171229512031118584140d241c1408403480d00340d050000c2501c0c580b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 838871420 1250 838870170 838870189
    0x30506010804110a0e0c031806040f0f1e05100513020a0e1b03040606240509120f07141c0b04060b010513091406030c0f01140415020a11 60
    0x2050396095069116500c8040302614020446a8801c01448000512005069101e4400c518000d03d1507182e1522810b80307000c03a51b0141140c05103410850405c80001c1c084150115a84e402c20300c050300f100303014a00006c22540e10b860110160b03c01445c201d082140c00135681c480c11803489800e0190381c07540076161601110b1001c001390b120b1801e0b2400e00980d040715104640c400c003007811007081c018194034400d01c203910965041e00d805446c1c034030a0000c080100d031103410b119104c4502c1d40c4071590b4004010100e000f091221441203102c003039410540002085000581c1305010140c841c9555103116209000f00904011802a5503514100728640d2500e100300c0007080e000300340106a6900d81d6120703801001405402414406d09001840c80300c2203151420016000724200026034021120a008041d1b0000300a148641c0c0030301c41c4002c43d0b44500150b107041d43d1082c02c1c0301d1400b00c1070b00c05102c0240504d400400640c81200780310340d60190300280e400f0b0400c2c0a0100c9403c1c080c5850244045242d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 838872670 1250 838871420 838871431
    0x906020a0e010f0c0807050319090603051506040e04030c12020c09060303030103050a081c09060f050a0b060a0311120f01060f0c0302070b030604090606030b010f140901143d0305 78
    0x81300442e0510200e55034000038010180725000362494400050b1061f080a210030100f080080c030910024004c2c0c0d03825120b411b030000c0180800400c603083e000300150f414820fa025178040540804041020103020b488224007141e4006084031300741030a0040250784455030341c3c14030300c6145460042005818040103e906803134100c03010b000f00d0b4800341c80c0ca0b1829480340c10162005250307c000c51680c42c8851145000f00391040c0801700b02103a04003c00c0701612406018150726501c1c00071814401d0752003004035100ea407507506001c100c03000d5400e0a105070b03014030a03031000c2c030540e01401c00c000b041764400011b040e2150703912120302c6184401000c5820f401a108003d000da4401c0e1818409500304c0b60207140c1c0030340e000780041081d0685d0b698040954003664401c8803c03001450041c840c916658030640041d00003c1c5402041601c0c500010341030b504107101d240104c049001000d00c4940b10f4516101e040c40d2030305808103000d0901010b1390281104061000c4440e500496810a01c42c072a000e001d0191 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 838873920 1250 838872670 838872677
    0x613050603120c0a050601320109030b06030705040e01020426251e3b150d031707030e060411131d0f0303010501020312190906020a0e010f 61
    0x44100614080c2c1d5400222000400e20840c4c5058000480421072240031b0150300a450190a800a00d00f000c5403800c40d031115103c0c080b2440d1030450703991145000c81220341080d004002511010701083c100b10664200076000350038003e12881c111340540040c411140c3c03041200050700c1c100c00c4950380e41d1602c50b00540c129013001d661400c1d040c0c403a001030480501c000320401211552400d50006621049080c14200820000c0c2000603050070500b00d0036610701c4180034082c444040c0d4041c20400104e8080c0c05c00c10b045200401c00c80101e4003015140b2120140c00c0000e40183da080103003034888450f50307411704c0d81400400100203d01c6809036039a03c00807072006028a0311076550b5140d01d8030620303a0113500424405000d0744581440d006003885200e04036100ba6142c07103266141400c048041000002c2580100010003040c0d81c00411a40d448d001d081c1141210f44400090103002e140008800d40002e00300050352081c062154002c1c4a2410151180400c0352030040044d16100000003461012 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 838875170 1250 838873920 838873933
    0x2040e01050a290409050702011505090705270a030812070512010e040302010b030706030b011824140f27060313030c20030f1b0607140a0b0613050603 66
    0x4002003685503d1401040054500300380d16120444100c640c2110090300503034481c00310031107100390b98540c03002620701551081c1c001c0c031b0509000340151150840d0035030100c0303440320003810302e4120701162140d80b41c0c001c01d003a18203680c07410240c071160404409024441e64000204808038020030444204003400c0d2145a1180c0c41c0804042e05824000c0041d4199521070300a6401907805002440240c402600e0000c1e004624200040145100040750403140c28003160034032900c012404019004c07111900107103403580103040c044558403200c19129990381808620f6070700e001101d0003d0a21130800e85525842c03081c00b6042c0b280c0d40303c181860305401040400100d04140360030641050704600905200d8004841a65142c50f54600c6080707120380500810310b681c0725894180310f41042034400030020078400403080d01e944803110548041343e21504001038580c040040390321441141c0240c080c1903c1c0715509a04003100c184d102202c0c0e2601c1900c113400c426480e608244640342c003405000e4001c040f03 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 838876420 1250 838875170 838875209
    0x60c020a0e150a0305030a0e0d020a090b1c0503030f0a020703090612021b0f160825031e03020d022404050c0a0305010906060f05102001060902040e01050a 68
    0x6600080e0064020509501c9404941d071075803c0ca00000710b2051008640d82c000414008000c482202d401611410118552501503a10002414180c800c81140011407840710000607018421140107a0bc100100500701414884c01002940c401e29080d088845943e03a0008041c1c12441401801804516840810b0103030340d02ca4811030319440a054001490400094000b606200d540c0181002940c0320108060349003d060180d020002c04223002010250300380707080070346c54200d030740341071000031194000c98840203031481005d000440d048140344404600c00307403005100d00300039074040d0098071800360f40d10349051000030f100000000d280d2860039100441c070010a40580060800e03561840b0344041e00b2102d9489069100003584240000110054240760a8069400d203500c82e0b041c0708402c040c20040740d120900030421891080c0ba10890296103c15030901c82030b0000c1e02019190b20300000400c0310760050380100261400024980c600346e030b0f40d90411212071680d0280d40d2040f089800d0040707 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 838877670 1250 838876420 838876439
    0x201120b0103111c1109032a09130c0e100e0a0f0c090f140f06071b0f030c09050c040b0a020c060a170609040203062208071209060c020a 60
    0x251140414500464420903410140031140c01844910341ca45540c4d01000c481c5450300e204584500f026020303018100800d0100098844040640e00340703028040a80140c1568941c5154008202c0d00500c1075219080948070030b000b10800b501c0c1144c803408190404544155902c2ca000d2250790300344c00080d5000c0c00c0480003411344070058813035038100c1d840780340c007480303000c80e601603400d002001d55140304001e45071503036614103000c0b80d910040c80126406010140c50300c800600d814055000d50b5090341e642003604e0440c0703510060418281c2107000c502e00c040780b40070704891040c2c00c07a4020031011a50540311403d14003114403e991240340d0010401041040000712405002c0100c2d20380142c80c414840540030444a40c0400385010020300103000700c02d40801a141781702d03082141a0382c3c201161810f0380c0480ea031000041e2030503c0e121341c08051542c1004184500303904103580401c200340c9800352403500c2000400b423005510040303004130002240031803091100319a081d030000c0099104d41e10b4200130780c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 838878920 1250 838877670 838877681
    0x1030e03031503031207030506193005060a020903010c050306280e07030f1404020d03180f031401290907090b1c0e1605091005120a02150304020112 65
    0x107940601042c405c42d10801d103a0405184104002d0301e02080c0751803c03400708402002750880207412410140c10601c000c0d410046041c020703200d0507040d80320500d41d44401421941d2010b030000c00903c120800c010b02c1c0c01c01e64028004605040e0020320500101c0301050720345005c101c4900d82c02c03181c3c2000305030304920480c000000001441001c8030107140c40e5038500b10581411200440032988401410040c0711443c40b5040076003006c0e00c000d0313445003400d600003000703049901c40c040c0400070742034000d00740c1c03400c41c8200340c00608039400414040ba5903490300c1c906074810721162003990351800340303020b440380d007520325000049041a540b1150b03501e0000070002030705000380c10102007066412010030700c0c070040801000750030224501f140110140c0c00380c031426501440c6003242c4a4001c551880c44006d00b40800c441614012a483c410654502d403408502480540c0041c0e8850501910505503010105008860500a03034405090b4812419040d805200030b5800074000b40400c0c010388001d1107240d102 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 838880170 1250 838878920 838878961
    0x3031602010e060a0c05070504091e06020d020c06010509420a03050606040f200705010209030d121404030c11030c0901080d0e0a060e12010605060301030807060b01030e0303 76
    0x640b031500740118169401411204011030191144c140c1400410010390006007130456061156031450b0340c8a00c406140b890300f05041c49600402e80f0100111901a40c403d440c0e80101191500c01d44400c0541c1c4100a1154a00485d89200420041c0e0584c494841c0d40441c0100c11911800003810a80d50401c108001860112040c5100302c40396640e0107408002076000300c0c0104070500300503003003104642480e01a100c100349000c6001c8580c0074910540406603403408a89603d0700d180341451800b912a198526a00d401106694518503402c031032243c0b00380503400c0c0b007004655210008c1068000060310041c01294400c40b051001481209842c0d0b14200054240e4079100b2110010400b440c2080c2c004203440d8001400390340e440e0342d102d1140c1035505401c603075480c001458000054038a00c0d5151000b80103903d02c8c8045450200c094014500800000c3c1c409640da6a4a0409110980003040b044801a051034a403c04540c441e00402d010350b5003200203146103407a014072190701d0040c21040b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 838881420 1250 838880170 838880177
    0x1020d1805060417100c0206070f170a15060509010503190923010f110d090305041502030a080a0902130f09170c071a030a15080a03022a0303160201 65
    0x10105041c0c5078003024000a0202c813000c1441c2c4140031944500b08800d01c519131040925190100c1d580d246d001803010f40007442c0d0b0500e2920000b900d802250840c3c036144490000301010414001d000d0420f60110b03e40030298268104d4264a8100480d140c0c82130300c200c076000520610109050418112014a030781c501000006501202c80c1c1d105d69400c0d111008003d1a55042840d02d4049803081c0035440c4603c401070010020040c00c201401310b140280c425549402c0d80d544000d908250284044178098802440c010004040c6c1e000000d540e503200c0369000c0009004500803d00c5c0700c1c402e0191000c00b642c020807016030742d00391414403402018480c0040340080d4480030000003180b041040302483c0403410100c0d6903265800303043c80e864040750360300c14505056820440ca42c2100100190382d04450311f0a40810340142901c41c11020a40c1c84c0c1140c041c43c025162120201034001030788001c0712621117075000b0280d42d188581d4640c0b101c0f210b003032501034104000d19a40b000e00000700c081420f10504 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 838882670 1250 838881420 838881467
    0x30307052104030201050103170c07172104030c1409130206040f031406070903031403071e020f0d030b0d1b030c26030a0507022e021e0a0201020d 64
    0x71807490300480585081d0050b07552100188103000610b4400f100d01a60200c070300b80b030080030035141d565a100070301c903494811107410046c04410030188241a41021180c59612001c203281d50146040e910510007118a8031540d040003c907005802103003c86544000d0440b40030342c2d210407080c52101140f1074100d82c48081003001240d11040f000c2400c0286008101141004a08595651501001030302c628103010341c180d410400a40d00400c0800c41040c0c0d943c81684980712000242d900c542c1045a524070303a03c02c43d1440f0700090780040d0600c19881c00c001100c87e26001c2401c2a0201d6507102e1040c4c0e00b00c3c42d612014008281d03406006640302030b080708241d007216525110564640c034941c2064425003805c0c00c415440c080101d0070b0003008034001000c0c0d8a84101c6110142852140c01c0c4000d004803100388402002011921260340304620000b090031501c550742c00d000f034480c41440c1001c103455603000d12207801c6841c000303941c203c8164107800a003540151180281c403c01e554455120400381d40e035 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 838883920 1250 838882670 838882717
    0x513081b060106020d12020c070b07060b0310020712140919050301050a0b010207080712320c01021209060301092d02121e181615081803030705 63
    0x108903042c002d01003640070b49107441ca80300000b00f0b804090044003038400e00603c6080740460b0042100402c6480c5641640d9903010300d403519030b0103081c0d1285010390500410100a40b04150394005010842c829091b4101008811000381d502400c0f610b0143c10401c42446051058100701031070704156002030040b01800740d90780e0006401d64000320ba94404060303e4a0100e0714a50301013112501921001000d03080c454180790a0b0220b600d84984d010304203202d01e40480a0986001003142e05903803129000c24040610f02c002c45640f01a00c45089006206400310030200d04d070044280c500d0b804000380282c1c40d5920b0300c02d0000185c9901c81a2040d140407079480b803000a00c446100504082c4101030250302c44034a800302d00b6440350000c0120034400d035003d4100f01d52440e2292001c2c0d003c0d44d15200740000e8113044182031b180000f400ca0b8140f8070b07115030b0350102d5141d00721840c009502c0d042e13560380d1410790340ea4411000c0c286030070b900d41c00d515030050000c201d5103401800030300b0400c0c2c5100000c05c24850796 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 838885170 1250 838883920 838883923
    0x10c080a0510050904290910110c010207030801050a080f03030a0b040e0a240614043215010507150e03090d111e060403060b0619020d0807030513081b 66
    0x2900d04075000b02c445d03440e129401b400c0a200002030f2890100b8090a460808040ca4960304841a8494510340c0d540d00081c09007810340c1500d0701100920000c40d101d0616240242c600c00c800e00900780300d44844070380000c2c075040004e41e06500095080c0a5420740e1114000303203014117003200b0501c1d03000341c4030032640c45d000004003e24072085014030961b8109000480c020703c1500ca414401403e541d0070000c090180704402809010030740c101380d4000803050703044603083c80780440e9080f0240e0384481c020340001002800500041c00713421944040c510143d041c40c011b40f02c505c1140002441142c440f542440c002449500c4001d46510070801d036407170700003400c0006070070800d4150101d51802d5250404499810000d03090500c410300c0060a02807280c240002840e50b014510009020300c0d1101607640c1245c856000340e8a0041e038a000e401e222020140d0b0103500d4150200d20b15000503004070000300e299202e401200e004019800318001101220b848a1a40360300000b41c5880d10356148000c240d19010 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 838886420 1250 838885170 838885189
    0x6030c09190e2103070e0102060103020609120c1306140616120201020408011401081e07180204050604080a02090705070803222a0605040e15010c050604050105070e03010c080a051005 80
    0x168003d00ba40e80b40f40110000d04203400301c00540e030465000c1c40040c00140c031010212000480110703038071090741d20003070700d03940c640b950829101c0e4112048000702c500c0c082d0103400039010b8030035900900f81a01c44410502809010742041071441c411000e90b040080741849442c001c015074507200240c501900e43c140a42521602c41d800d06a900f14800108170301c10051064007503140001030801c030500303402d190540d551102401f03013022850a4111104070b8559582c103c0380180000fa00341d0ba101d40c0e582440544507420100d0582c010018200064420fa2041c011501419407005000b42140c0301c80007294508640e403200d81301c0d049149448c02011a0030b043c000140405c00500080c80362510b18215095a030282d40118240f040a02c0140702d0070220072105680800c075525050011034034080121a0481003d202500c1c5004000c1031005005041d007005204010700c0d01e0300c01a501c1d042c02410700701ca038aa05904d0003c1d00e10804140b02038515001650006900006001565201c1e000a0040070 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 838887670 1250 838886420 838886473
    0x10c14011e0e030c060f0a1d1e16091e050a0501050a090c02030403020405060f10030f0b0a03021f030e07090501030b100f03032d0201020306030c09190e 67
    0x40c03910341181c16003a000d00500d0103080051029500300110410b00941c2c07100007918440c07486030010b0004001c04500c0d0f001305c481300c086240700050700501c1007a15885080c20814200710070908600791202860000d01f030003003e0b004d01c5819209510b01034020380184605402c41c1113004403013030303020180a0030b402064090311030700400042d41e51515081142c0f04800b0303400b21070414106410042e01c1e54002c410340f4101da405880228495448400040c00b0001d0548403660107000304001c010f803554154010708080c40d212604001800036081045600401880025401202034102070042c11101d5881244814103040108180c10041219414181039420090025503110010014841c0c9003003904e80020340780c0c040101c0542030110303445552403640000b40905c0481e10a21345280f41803119102c1c0710490708840c2c251440c0000703000b8040e5100b5501e0318441e00c0745800a104524042500038000c41a4041002d05035880c500c2180240c060706e81c41918500071641100c4c81c41c0c641c82d02021022 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 838888920 1250 838887670 838887701
    0x1e0b21041a0106030c0e040207060f020c240f1f08010204060c150b0619020312010e042f0d05011d0a0b01080c060a211109040c02010e03030105010c1401 67
    0x3a850040144246070050380300f00c00705030030315420b80c03251504000b002c015190207a90140c0d0350821420520302809103001307000d9030a44001174a01981c070001c5440c4501042d240702c00c00303075402210f03050600f1b03500589802c80d01e42c80c24404294120040e1640401d00c14600c188031004070b55540c1d0007400c80c2c0295201c44041120381881c0d07001c100c001c100f1001c545030802010094031108001040c0e040c000c1404640d50031024001e595031740c030700800030389011810000000d5541c0d03842d48a81e10350380c5000d0b142100c070f1244e803650f2100e11081c0e05051074070300b0320101c1481100340605403c002d0020304114040d00c03155a24103882c130011a0030005403880512036002403000070b049151981c44d460050f801011980c01503000411203030348079401c0b2410b512a61914051101c00703084d0b41d2240180301c5d110018403e14181415500321aa2005048a40000c031000c1110020000c4c0603401c1e0b41c10300f1100c000075002080180141d6000340090101d4034041e008003007031307005c1d1030b25604c0c00c42e1030603100c0d040c00 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 838890170 1250 838888920 838888943
    0x3050303070906050301030c030209090304030b04051c0c020f0f060d02130503190305040612020f03040b1f060e0910031a0103120e0616050f0a0803101e0b2104 70
    0x4030760b003080907840200000d14103a8655071441d19841e90740c0ca02808001c1c440d40c001000300d800320a0030001d4401542d0040c16903400c608052130482d03078441050340d03941c285150b075403821a40c0300d0081c8581c28902c0e402420a5100509003010442d050510b45a8254802824000d80b86802450b2029014040d500d80030440300c1c9082500301860801203002038451812090701f03140c00660b1203410b40d0b04aa40508004800410303088131540603004a812540f071a0b50007200300818044203081050291082d821480c0f400f810548880701c00c10f00c07500480d03001c24206480c80c031050400c03885a039840030038100035080d855160b903105540c20422820300a84654100c0040c000d006005401114000c1c0908000c209145104040342d524010010511080500301c0c84480034000c041c064400d034415844180c0d0b00c916800c1c50039407541d800c00d8551402030070401001042030104041105c5a035011840c000510610300ac00004140c2d0180c89081514800c0d00a103400b0081110505401503101e10717240e001 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 838891420 1250 838890170 838890181
    0x1020d0f0e07081f02090301061802071106162306250c0c090c0201140a090b0901180b04290603060906014e050f06040b1501031503050303 61
    0xb804240b074015044a40000300d1031501d01c000c6944030304000da82c1c1180583c036241520700190061503281d2040908954040700040201c013558000c2544602c611150202c03121244144103403401508000b41d2088012100300000c1030702441d00c0c0b0884c0411400361417201b24240c8505040001c25a18014001004050b401103400c041030b210304800c0c00c5103441341001000e40ca900e41099000d21403891840d41d50000076405a100390400320a02c1c0f12040d8548203420031800c40300050400da0801c1d02c1c40390800f00170820b244018010040720982c0b41c030351040210740c0c548603a02c00f0007001e00704a5140c0d0140400504440c0c404440600d4501907140c4c038400c5190180505086c10f00040c81d10701e03103800c41001032024502c00d14694076207a0204152100903240410f210045940c3e84006141d031220958400c0408090136850703940052280c016030300c20880c48450207646450640b8001c0c900c010345000a070200040c103480c4440020145804100180421400d24a4150542099805403c00001c11a = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 838892670 1250 838891420 838891423
    0x80c1309061d0601080303070801121a0c09040e010e0703062307080411060703230d0230090a02010c060212130201030c090b03041202012c06010518160201020d0f0e 72
    0x70700415084006e107241d0b18186400520031101405a5540d403030f0010884814081400043c5990000c214041c0400e4104581e8000440e002004402d210b00e0518003511b4030428103009525011000c8002403070814110b540705806004c401081d031040c82440799440b040003480e240c100e40100c08035154011181010f007010502a01d40c081c045004100410181000945c009202e540c2c0155000303400007174941542c2c0b105500d104a030107900c400350021170880004174003603083e212028010740e0714000040c4070395010b0000400807501d08109400812a000c052f50240d101791006074070401d0010300d00440c840000328003031007d40c0d240d084a42d0040800046581611560741c00c03034581d0400450003498248007000390b00c40100000c11540c840b21100c50410b001f50000c8054100002d00700d041001078810f0510039480303c0e0819644c5104210000882d0704008412406001c0203520038403060390703446449001144040c0e1a00110b41d401c006035204240184256150342000c0b64000c41c82c0192a460203 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 838893920 1250 838892670 838892683
    0x82503030203010e1302060703030518010f06152a331d030f0702040207020907080702010606090b0a32070218070c0219030f030512070306080c1309061d 67
    0x80c0b0201c4600d40a0705c0940c1d152400d86102307584c075190124080e9140340d0004a04501c40b04414525802c00c501d20000e407100e038010000341c1c0c0c5413170280707845040e8039207003103494405115407250000c0008510703003010610088a4240d883c05000341030700d60301d5404180010700c3d41c005558218004801c0d05030f200d0030002d00501411041c00c02c200303082209080c3d21603489100c0c0418400482c10005117180c115111a0103840805030018112039507440d00c440041c000c284201c403444010b51800201040d100c0c05020800c05492480f1291410840d408034141d8450040c0550715500010001e182035007160105201180e402c4900b0f5101d86804040c8144000c07000600d001141c1e0a100001f0020000d5011f501840d803180c04890118403030201e08558001c0c0c40c03581d0006421000d502c03400c4800d2540103401401030030302c0c804152043d65038084003103084440ca4011803019802402583d040303840c00702030b8800b40113000d4200003178801a42c1c1e180070441d561000c110f028560382d800d1100da00c65003030081 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 838895170 1250 838893920 838893931
    0x30e100e060114040b042a0503010e060f0d0501060f26030d180b011401080124140c0712020913030509040903050f0307090905130c03082503030203010e 67
    0xd200c05440904415103610050103420103808900d9180e92080d5a550060100766201070700400a103151100030403000400d104170f0000d01004030361031840c0c182c80741d4201d078101c0d04208041221522090200042d5003140c43c0d201e58025070386948280460801c0c824680200500400200c0241c0303021100d40c59801200b403241c84542161013841d205610100c00c48a07800c807a01390008942d540f4104519a58551403400b802074080d4000209040c0507034040460008800d8a40300110f0703a0720040184042c410300122a40328036032090136141c8174050b4280800ca548014101c1d82007110200380070380340c01900d03802a02207000441d43c580640c14640402034002d2020451240300304200c0d00c1c068540e21801c0c000c940125610300c9a001031510400954044d0345850540b95a2800c1c41500104807407400d01134000c40c00d24010105000c50b9202c400d10300d54030b50010780e20030720a00c0e54440046a411061801c0b06c901030058100f40000d0046031140000b03480b81d200140c40b541411842c2a0680c4000c04 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 838896420 1250 838895170 838895203
    0x150c08070206031003020306100806010e1807080601091a010c030c0c05030a030e12010b0306011e0e0a0b040f1e1d07030503030108060c1c0b01091a070204110a0c03110703050d030e 79
    0x2c02b40007001d0045004d42c10341d101004484980c1e21114503602c000d800c1012072030500d0040c00f10200d070348600400c00c0ca048035045002030050740000078054016100d00310303001c1d001c0f8920f6000c4a001034000c01e8122503260041d60504100c60350380b00441c0c20301055a13403c034005040c01c0000b03000c5160410201510400c0791008000d80042c034004280d981c88103001d40004c808000c400050161602c2034010040c00d03482241720810308000c04203038040d00070618418415030138042c25124a034545c2c81120040b03281d40c14154a0590520054002800d0340030100d035040f41250180103080d036080200c00000c503c5040256560340c9060540307070a14a000d0f00080502c07804220095203201e01d01d400070300c041c003040720000fa800034007801680c0c2c0703950b25800a022070745d51284624064520501426041d070090320700f400440f1103503110399410f12443e440240440c075514000d6000c0b80c0f08030701800880e40000304850f08640ca9888042c030301038030f44642d90002600c4041032482840c0c14072a81c00818450f00 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 838897670 1250 838896420 838896451
    0x9030b090d020a031b06110c0c1f110109020a08030a09090c050a03020318100c0e04020301031a09210316210c1202070c050f010801150c08070206031003020306 70
    0x2402921822640b201030208000340384415051221705441002055011104014491000c0b11400050b003050030900708c207000384000803000b4105407001480450322500202210b41044505841020080300c29000c291358400b1a0001a12240d40070b2025001d004002c540b80c0e40d420340002c0002e111504415a10350501b520b60340d072180c010003174a03082660382c10056107964400201c0c0b80c0c0b940007031040808a2103080c0d01d1859040c0b80d40e0000d2140c640a03516207007850300301820721040e071100703100041480c08140d0004943d400e182c1d120f26003055500c2c090314100d00c0c2c0511180010314000c3c1a0007070a03200041131122048124070441c485010a04080186a401d0718a41d600709620400030b41c901500e540311082124818850001d4404058008548400607410590754940881c024035029035201e1650b4222903000e84607880c100c80c1d1038100c1d00520100810115a480075910003261071804c1800b8480044c1e07945400f440c0300d001d52200300c204840c030307500401d0320305400a00b9100d15120001d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 838898920 1250 838897670 838897693
    0x140408250b0703020c0f0f030d080f1b0322051e010c1b0b0405070510120f0525050909090a020307091a01080402180106091401020106180f14010609030b09 68
    0x700e5100d001034030446c3c003e0800c030250307070129613020102500d9a500d409031003081c040321074021440501441b40b40d9820701b8681c0d128801c507103402100e49001c00300801e003400091a4000c4001150440140040d42030400908603511146001d090300e90b54580c0b00096010904020781c00d04c200b000c3d50b051032501803001031054041c40324003200c02c00301520020030000001d082c84410840000105006401404500c0d80b9480090003840420f80158255080c0034810035420001e000f0380d40150900e04000c00503d580500121b6000000c250070818080309000001040d0f0300c0409035481107403640060030744907040388105810079015400c032600c00c2d0300d040104800d580c4038000d0f0845903d02800d1a43d030a44460002480c4600d00000da09a0764a542c0f0010546940c4101100d00300c0f010001c2c07104509507154016801e0b01c156002d98000140740d000340804900540d04141d200d40c64801c0005601030500105540e4184240c01003008913000c000100100400200c1c45940582500094144041704 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 838900170 1250 838898920 838898923
    0x30318010605011d0a0b0d090614040b07180e0415241202120618240c16021f0e221e0219080106021c140408250b070302 53
    0x1316180c0706050b1140b8402d00302a81c480c80180b00103050711105407502e4000b80d68814010301035400007111130604128150903a21003d100c1d07980107550100710a8220340d54044110340b034540b0702103292140300c09080005020600c00741903600a038000c0c00c52400c4400f003880d0700b4003070741c07900718445c20594034142ca215105010601c01c40d0039503080d000300443c50041400014038011807021390406d50301418050000d0345e8a40580008010300c41d0342550684906840810800c1140c01200c2c41d22001c0c0340700041c0b000c4400401050511b156098440f501c0a65402050b0f02845003104482c01400000f2881c826542003002a00782020403104203e00c0b6209442d02018440348200040030141c49403840300000380d8040042003500c100034421500da00e031410f00c0c100652882c001c4000412b0908001081442c40400c03504880100d070b00d0f442c141811400021500301d42c0302c260703000c090f100500c07000c07900e038105000c1b4a00740e90b00c4001c04200c2c168142c0f21030300229855449003000302801c201100000780c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 838901420 1250 838900170 838900187
    0x415050c07090b040b04020409050414031908181501090b0f011218082101120305070b0601020c0a080102041a191202160b0412180b030c041703031801060501 69
    0x2c40e000104000040b280400c01a24408100590103400400c001c2034150782c0354031031445103019078242288420000845d035181d03c11000f50062410000da09010300b030b405a42d0060b0015241121000d1415030140e5140c10154591124100c110710f040041241c0d085500403400b01c010102c0c2e500026080c002d0010f490490302c40b15040e10b09440d0403180a0b80304444035450007c0e40c01400456444180c11206507240c21040d000c40f00c0c82d448023001160f840031460340303d60341c00e0741521540c0c42d040d0651580020810300800041c114850313001c0c400ca054944621003070080049e100050317100d50500300704240c821b258100ca002290018030400400361820480303190300103d40c2c20900c2da150846101280648562428400034440d50408807081000101d80a44214002c16030705000d0600c81408495003104101c41000c035919503041403160b03070729010003550080e003c02034542c50036540c3c1451480300c0508102c142003d4101200b0441e40301250300080059020000003000554107040001c0c01490 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 838902670 1250 838901420 838901429
    0x30f111b01080903040b0c070603060603060f090e0a080c0d0905030a051510241815050a030906090c080d050a1d0402070b012303010203100b0309150106050415050c07 73
    0x10b074040f81e031800c410b0044801601d500700c81d01d070750340091188aa0780c07111684100000a8504000055291310a201e41c1055070441030210005510740884840070b40232040351110a4012420174038002074990b4010308002c0d48070005401c01d00d4028034060482401588202d00036008480d035a000104c012441c1e140c41c1010203207806c0191600c0c0b01400b0380c4403550704010300b28580c0c2940e4005090824040c074440c50041c1d500c1101c1528840206100b0030014854821182c08461908040034040e802a1100c0740c0c90b0710340040c0e00c4c0d915842d280180d43c12100152040244950140690001031080c80c110b202a414440e20342908150001c4c62048100c6250b2414515090899072680d9641c0454a02c1504000c4148075540c441941e2490742d44c140000703404503030f119191081c4508040c0281c0340300b40c400c1c1041c03812181c034042560320694401083c0c1d145500070304d800200d601c2c803910401c038041e101d039949442d1114100b05001410070b10b40c245450501c801400080c1c2c203184002420015035 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 838903920 1250 838902670 838902677
    0x306070305070c0c03030201141501020a02090604090b010e0a0b01110606040b0f100e03060a0902090103020f0d08180f010302090d150227040b0405060a171009030f111b01 75
    0x550342e000040700c100081e15401400c80c0803014000041c558150070800a465800e550b0b24855101c003011117014101842000380560015a1520090715108103090b901c180c000c0e00105029031941cdc2c0c1c4000360304d4260032914285000c40284002c50642c0d2040b5000c000c42800c100f03040c41d1400300082d40d0350034001e003e0303031040d9110180740c800c44d00c41c0498020301103000b03840c0303c54018011102500303101e43c0882c928000d215240c0090382c87c10f0240951a40c50350080c0c4900d1380c076402c540a0048418140b410b064104003054000701c00074410b43e00030008134503910509840411350904105805040b001e1543c10180140200702e15507442c00d0095203220391002221807041c600c5889800603024041c41d0703000c6100d1840401c5103044c2c0056540250903801c072410050091203400300401c40300142c070060341101d8101c100b400f40da0020380d00b074080401c08104454251914491460642d008540e0440c00241e110007503400144e0080f0314202c19484800203030800c42c0000e030102145401d0402400e040 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 838905170 1250 838903920 838903931
    0x16271409270a0204050a0b01020105060603060d0b0a020f07140111040515030403031d0705030f0628060b13330302070804090507090812030606070206070602130608090106120203060703 81
    0x40740c03000c00424041d42d50140c000d0100b49030010b8400e0040890900d628055400c1000080035850f10301e007100e01c14070009140ca4058480f9456680004000030055480720b603007000009807208150740078150b0907102e0744400081c0c01d240400242542c21416403455036140c02e001c14040d958800802d40d41c141c100b00e041545030303503035418110050201003600345c2079088107620840c01c07003001165400903030704141c00322901072036500103c40c0c2c2d4090842782d0300407081003a188ad04c84205501d84480c040d500c907082c0130135243d8072000c402c0c9150784140700455001810301020800402d05144207407540841240c8a180440c0c0000b94174000001c03074503502d04165001620904000c0c04c0d00540c0c02a10300000704021317a00c0c05080183c0752000c24042c0c070445100e641e0008090302600000c0701e00c242e1010b06818104140c0741d0a008080d041710b01c00b110708580a00c050702402c001042450020032171980c1d02c0445060810901e801c46103207800400850140c540302c1009070300c1c001442c681203040741c03500180 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 838906420 1250 838905170 838905241
    0x30b180408090a0807091a03060a0504020a0902040e18030a02121c0e0f190c050906150a030b04110403080715091202150708090616271409 61
    0x40342c0c401c0d01c00050b8825030a040204011000044800c2601d1965200304038640d0104070b01c16000c480715802c0e99060740120001042c00d41940c11541d0001e102424680f500c80d210000c0c9402e80c1c101d40c200048002d074071400c20103010254004410a803c2c0803000c1c501c0c00513065402500d0f910213040100030800c0018004002c0002c0408051a18180030001c00a10b80a2549a6116030030541300b0101c074803803101502c600c000c00079031180007154071240941c84946080b05000c07002000400e619030001060200384c0d40540110020301e0408020395001a802c45840204002c480e03200042510041050009000064019049483c510b41207210318034154540fa000d28007070f00407004014440250b8105081c100d070380000e81400000004010f03070f111507695883c103c900d180101c601c078010380d12120200307480c5070301c5041d032101d0000c9600e8a00c80d0306000c0d080104070803005d642c0ba0440e00e41c9202c2c0403c8030b0307a941d1044408e040002c42e001241030070221182d206020b070081030b1015540e0031440c400c4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 838907670 1250 838906420 838906433
    0xd080103020d1128050406050f06031b070b01170706031e0b0a0503010608161a0f070203071502150a1a010f12050408030414060f0c0a11030f19030b1804 67
    0x11302c04442c180b00d00300045541ca02d04800a0182c030501d8003580c180f8002040c103180104110560314801740c000742c115513524001d05040c544a10403c16103120401182c0c01140c1980d2800e80680f04500074080c24150a003d0700c1e2034007040341c6c0007508141c40d05140c40424005502068411928450085544008080001c1e100d000c503602c0281e2640c03030508005200f01001c12000e2001c010040f840b50070a84c1c40d66810070b4404c4440079014504000c104014900b503900c000380800d5030003d02241c4d00c1c01d0701c50010003448642c4200c000051303445450500100c8d005c0c90102c59020071100b109002054004030751300790240c400d00c91207040c04000086121158420300e9446101c180c80f04062149003454140000698010f60301624040039010803038481507800582e0901903c0107664840d0030355510740106040707800a0620404200c00020040018a4100302402050b41e40c017a104d81d030b8400c030320b925040c01e2003a000e01c0020b060038602c400f5015516200709407204880082500700c696a14034000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 838908920 1250 838907670 838907689
    0xc042d152006090609030a0e0402070609051b040c020c0d02010f110d09030c170a08032a0c071512020a0318030f0905010c08180f1503090d080103020d11 67
    0x6824044034104581d000403000540c02c0c020494142514499110000d98503128814007d40d000400d10205500540d03043c598010300016008031400107103441d407130361480e06011421484d5a0700762140c0c010010a4a414411281c00a4242c0000e02016401e400072402c12175030200e000c0c0c1400500112101d441d4001c48004074000d40038426100326618120b0003a207003900901060f00e590445290209542e60400071821001d10510010803400d01180e803003240d00d034401403103400721448022300d4280306200b030070140348002d101025a586030078504100e01c1c50400303503070301400d01d0756a004200c44a60b9000ac1170106c0441d03540724056038840d440c04064010b01800c4808405daa401d0700743c0d500c24950b002e00d90148240490780d481204940c2c1d10b00445546881250291521038108074104c4000c0d0440600c205000d0040e1049640c0c0c01c0050000f140248240c00c86140c081c800000c1041c01901400030715074074041810106210f5040d03401080814040400051881c0001c4580d00000c3e984c21402 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 838910170 1250 838908920 838908947
    0x20a0201093317010611191a070210060806040b0c0a0c1106070b010e0a0c050c0d0e030111030f0f0f0c12040201090513022205030a0b0a060e0c042d15 66
    0xf80d0115691280d009100084403061001304d030080ea110307026104002c640403203509402206d07040e401c41c084c1c0f441d5003000001400302d8065205400100381d071a000d501607030009103410070150440b807400e410518000b100007007a15003540070420041b07403102d4204013000c00041c4c1111030052900002c20102c2c00d503126481d4050034502c0350100015030858225412442440c82440a11450f00c1d446800d40701806050402c051340d0b0001d44904007000d20480d840c01e400d00700240085071298001c00396160740c4c0d20540d115400e4004c09001c101c9040040c00c2c049030014107031142c1d10300720b00d4801d0440041e400307400302c07518a06213118081415684200802000381c10010704920212604842220095207c0b41c0b080380040300102c400d0f5002d441e90302e803120031164050050410700200359203950b1090002000f6907481561490301240f081034150905100d0020403040315510750074412020a0410800c407098919030b2403040b4140c00f0f8400300740c084100e07441c00c003000000b0208900e06480000c440d030030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 838911420 1250 838910170 838910207
    0x5150c0d051501030c020d09170102070b0c070c080d0503070813151505040603050d20010911040b09100902030709080307110a0f0308031f03080a020a02010933 70
    0x10322020000c0c02c10100c0c0d0056007624100318241100c1410fa8a5008643c0944049074000c00b0030003420040e00c0c2c0c81d90030803050f00b000500d00788071503441d0261500b05a44440540760040307480340c00c1010f0349503076002a00c80319000f0200f0105024000b001880b0003001042081103842c08500c00411441041c101d00f0b03032000f03581040c00820585c8a00800740f245c850800310041080004031400c0a00c80c1c10141d90308000a4803c1c400da5420035074980340f070f2103168844001e0384800c4c052001400e103c0d44d4400d6100d18210994036481000308815260040f01261284503104248048000142c2102d400c50303c8100c0c0251722640d81140c1a581000c10b6071190743e41d400000f90040070820340c01c908100c83c240072034210600e69103c6003205020001e6001c01030910408002003000c01800040664010b05102c281154a640341d030750b6004180c01201d00040903034001c040050031582c210380f45c0009402000b54907518142650142c1c1007002c00c20a50003038454030800010500b0307101c0c0c10ba00000c1001c091 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 838912670 1250 838911420 838911431
    0x50d171005041503061e270f02010e0a1d010e071e1e080103021302031308092e02010b0609180402151303060513110111160f0810060305150c0d 63
    0x45204821b0403100302e503501d1844c68040c84500c0c1e03031100c81400610703c5009104038091001951800d0400d1410b00069040c005016102000d603a180801c0c0b201a24107401510140508894040303025481a045044c011442da13041000a980c01803503001d075100106000c0981070303182e0b4001e989030307890f80064950340c05054a41d840000c0c0c003c1c002c03034100c910a90303400d90384152580c80c91089000c140c8111106074950000140402c41200142c01c680400400360003002a40c00325140010103105902e110362074400014032005c540a200b14000300100351151860180e108001890141c5c03280108011040c5200100d825520b94102040350740d002c0c1c4000555132001c0c4101c08100308420300c0110b40c02820180029420383c0c203e00108205039100380c0a0f001400e0382c0700199400c101242d484650780c412001c540050551040e180300041064003091400607007000340a60402c001c010203400d82c80c1c00c105041001070000035001b400c0f42c1002001b5840c40c1c9900c9421070340382c400d01042c00070090801 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 838913920 1250 838912670 838912691
    0xf0206090a080304260a03090b2101060c030e0a21050304120f26030a110c0a0b100509010b190207030501020d0c0306170a0314070b04050d17100504150306 68
    0x1810540b82105d88480d9900c1c203820b00d003060302e55030106114014001040341100700503821549010302490210a4400501c5001403101010407401c260f000e48000f540440d181c2080c150404442c500910041d10b0140200b4100b02d840c1003e000300341c81400c01c400d100014182400002e20545015003141195820b01100c1030a1010400c154070000b5100641116068071150b040740c0c41d07040540040a4056040d603841140302001001448000d075410b4108000c0550780710020b002181489100e046001007505250000140c1c65000760881c90003004000d0041c1701c180030300c4042e03803440200c006070034140451420080f8181491540003c080790300220f40d290044415400c000040c43c042c1c0d50403c5601e41e41c5040560b048100c1034540c90541143c0c0d92440424401c000203102488000007452401800342d80315611540d085906481c40c5c1c00820780c0604440d4003040786141542e0b81e80340e1144d02d08114204003681101842101d1080740c1c0c2d81c410400d4449552000c000840c2c12504c01c000d480180c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 838915170 1250 838913920 838913939
    0xf03080403050f0304080c010302090a03020301050a0603051b060706051f06080a0f0b330c1c08040206270402030109050f010501140901050d02040f0303050a0f03090f0206090a080304 80
    0x54001191103009403c0b000c1da540e0340000903035003181c0301d501c0104000c0c6414030040d00203610454285030440e0280d000403026071400d0294501416a01d80001240340c6507040c001e00300f00103450356810803030000e1043c1103d607440c00256861950004000255500c2e1010741326100b84c08400c10170040f4440c0c820000b112074220319610300c100c0740100b05010340d00201d40c4100071503c4031480301e980071080c401c4145460311820814050b4803185040b0a001c1c0c454844c034440326030820019011a45d010b80f17208041c05039021301250a001030380c03e00d90b109041680c0029413178065041980160003d00c500c845c0b88200d903c5181c1c28000e00075004550b203503103410342c050181c102240d070510002e000030000a40755114540703180608180035001400c11429800458003a07010741c407d4031005800b404041010440d1480380c000540c0300e9200c0c10303541c2100340390162244543c03003444000e143c0303410407840201d4400d09400b604542d040710480da96050105c002844a4061f8100c1e002030306c13012a001c0307514000c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 838916420 1250 838915170 838915177
    0x702031c020706080f0f04032109020a08071a0a050412060f0c020d020601090f0e0d050702030d030e0a02060f1309060614130b03041e0f020901120c15090f0308 70
    0xc80e5400c0e10022520f452080e1180d8105460350342c2045a40000600b0006660b40460741043c460702d003000c1c044402d803002c4644109072019003500c050340c3e0f9000004624003198000000e10002c0c028025261800c52454880f22090000740c0d0302d40c10004041000911490403603000e00102d41083d411b030b84c03841c01d2440c024038200c824440348528241c0078458050000406c2500e00c0c40c02d03030040c080c90b1f0920440d107000d40070400c0092a042e131100707214600403400740048643e144d4566606921002c4500400d89449a04020107062525010410020f0200400d1f0b103407109805840b1255a6541c401c00110315204907030700c24080a41ca01c0000c00c1d05101f07a04600f04540c003d6036149801c0811800320710040c40b0f22014040003404a100810400d904200a0b40d4043c0c041c0000e0171441d60074228001c191041c3c244115100c0042d803080800710303d44002400e0160460508805440c004c6941d41c2001903c0c40c001c22843c01010140d90114a00c5150084090070342c14010303c00260b500e1815441642 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 838917670 1250 838916420 838916473
    0xc0810031e06020307170a05041205180a080a0501060b0a090b09012c030d02030f0d0527071e05130f02271e150703053105010203040f06030b06070203 66
    0x1b03d0f0140815031041060148a01503904180030440d0420891015a100d600440a1880c01e0300724030402e014550b00e400c0c500c00100180800340c903110307000c0e140540c210b0312217820250000c031042c490401030701d80c084010421b5070505406555a05020401030780c01c4409650220180c0100e0b07200700c2d020305010000202c0483c4241e04940d00301c000000d05070384038000c40641c0070502d841403158001802007900125001003182040750f460700b42c0b00c803202c00b0f00441e000800c01d090b80880c50403c64030003100791000e1100d1040144c140d4007070920001507a00200b030002204440d40303540604603890083e03811030f618582031141c9141d101c40001040c0c242c00149000c801e100710b403c0d140c560600d118015496408400080406104441241c0c9004482e085a881641080000d01440121790003c00036841000203190503448208003400c0c500a0000845d0400e03811504107020400004a1540e40041038507254100425540328400100b029406030020107940b621441c3c48006034030481e2200c000406 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 838918920 1250 838917670 838917707
    0x100c0302071716150b041b090b36100f02010b060c150c1909080d0201060303020d0516060504061413050d05090d17030a0c0810031e06020307 62
    0x50601000b1000c55004201c400780d1000110040400013450000705480e44419640e40040da180503039021408030f03050314010740111120082e0640640390840c4a120041c090f100401d403030a000200da1740ba80640202800c60209211324940e11061000c074800100c41d0b00103841079525004400f8001c00c1a0354000b0341c1c1c405946009200003190521000b2214181d81103070042c10382c54440018070740c006000504c2e6800703200040c0541306c11400158100d00791541d05566003c001410701e2002801c00c540c00340b58409581c54802c00300300194012520690340940b07410180e0701c4424001601080d14003038400200000e03d00002c00040101543c0010303005202c00304008096902d50040c0c0030105240040034243c3e40c420065480c1080c46003000b4414a1009003200001400603034802000c2c030750b14510201c204a0200c200048103005102d4401e1045407441d150200d4207104c3c09000b8020824003000c0d000d4401c101341240d00b6440c810000003075a40c01117045680c0d144c24540100b0f40303101480040f00301d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 838920170 1250 838918920 838918943
    0xf010617030903071403070e0a090209060402090d0201030c05040302060304050d031d0a0605150d050607030b0607031403280c02070504020a2c031e1501180e100c030207 74
    0x3080004265245400d02900418a00341803c802079100c02c0015041d507810711440f00041008112040424080c5003e04004a62003001d44100900c281c1c008000d2806244180048845603440614517040300d81c082c240081e91341c40c1b102045540b84140d40001c0d401c00d4000040c0000c10600041d41c8882008568040100709021540f2000d1440500d61001c00b5500c52030b803000200d09180c2c4200c0d0404040d000310b80450440102042d14040c0d00101512950404400c03c0f4415802d4051603000300c1044414a180510558000d130010400350070140035040044002041002c503801407000c00c000307002c92603184600d0741c030012024200c100b00d040018040c0c0c171000501400e090094031079440c2c0b961200e1411036078411001e20b2004a90401c140055181e86070015103807400d01013641d40351151603811001000319601e0526040d048011094000b1016004118070303203030303d1100c0010380200d210202c0c0069103d4000c9180000c00c0089544203440c0201c0c03102c4807601076000307000780791040c10903004 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 838921420 1250 838920170 838920209
    0x120706060b21061f050a09060503010f0605030402031513050c0603100e060a090c0f0314040507120503090312030a0f1407030906020418021c0203012301020a050f0106 73
    0x88500030110050314102c848100700901c0040704a110fa8050005042959a80c000524030707010301403040540804600001440783c0c986c0d512040180240400b0706100385154500095000c0c0000c41e0f03c1200200000400400d045607000e00940000101218280c98542080000e0030300c1d054100e002110306105108591009080c81802d0340c0c440d100d0441301403402440d1038101d801c41007000303001607841605040302241500040c4500c2011540d035503500c20025440300405001c80d1030589100001180f10010400041d900280c060159403e26040010071001854103511314000c00c290350794180903001c3c3e0028044401d0f00518810703084032030280109038450407142d040390b503084115038a100c10b0800003002940250400c00c100c900ca0320b401803600307540d8907504c061142c2c20009614022740009046c000c0c9900344006c0302c104c19041504500c0d55142010202905840c6a02c0c504800700f4143c08402d01c2c3e0003800f004030200e40100076100b4030001c04001034002c0540380100140b18a01240480c03 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 838922670 1250 838921420 838921439
    0x9130c090e1603090f05070e010906080106050f0d0320010f05060d0b0f07121406031204061731150b030a17040f06031b1704020907020c0312070606 65
    0x1030141104800701200c02d0107201045014142203a000d4415010340392600740085c030200a044010900004108034030750602d0101010740d081640110140ea040440c10711070b540d00e1340c04455100c801154104400e2089107416030310131081018404075a110000b105001c0701e019045075000c94401d0008001c0c603a00c3c10208a0710082e21000034104034402c1001609111a07050303110340120450400c040f85108070440d00c810303101562628811074025805220150404000d5046483c2c200b0240609007810480010840072000d01c0302001480c1c40f002007240203803004c4403881c80194209586d02491201000e444614400520403580300761103200d100e02800c010700c1146040c0000034003030900340d895601e4110b003460050b40c504130108820000011076131051001000180881e44020913034402103522100c04004922806081c4101040107480010f221185680d0042e4100c8221080b40c550300d00c120f103420303080c011864161044110300920001c0d5413000c1c02c1001c1c070801c070a0000e0f0752117580c0b50 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 838923920 1250 838922670 838922699
    0x601080c0304033015150f03050403030f11070201230901030504140109140f030a0504360b0a211e05030a0f11010b130b040209130c09 59
    0x18108410a0000c540064812005821404000403180e070038584030b00c004244e001d0b050f52074441401d91710300c040c8210f0200b651000000b01210010b005440c5403082c4080d080c40700c5aa8820109540c0e00001010075000f80d009108000e82020100207801c108080404030b64410002640441d0326010303035039035a40710714469181003d00800c1d603500b407201c1c078070041d0054035018000306ca010b00c49540d0702100d14024403403160301c14015240740c00d120882c070007180d0030002d0706003240595804c100701e002d00c000d0700310040302c0865282500c0400c94080c1c50783c0e059404081d60910500e0351041034040da4001005420682001c6802c69401550701da80b02c0651000700802252402185070707000715440400c401068540f401c04405080c03503540b1400f5070b130305411a80400c40c0b0401180c1c210268500c019401300078200d4160040c8001c011729142c440019034840b0041741e0003450103031030707200b2028141c80ea90140e502d8801d000c0c02c00001031400103440303005882805524030010341d08402c000781c11640500388 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 838925170 1250 838923920 838923931
    0x91e16021c021b0a03050d0801030b0c070b0c220b030603070603020304110d02120106061e03090c0b130b07080a0e06071502070f08030403021006052d0102010b0a0e0f060108 76
    0xb0301d1000c3c144141040c2d10200303440201e6101004150010214106011400d40701040d035644000940c158504140f07100d0018042048001040c001c200c001903c00c1070b000e4001c480242c030a6200c40c10300890802c0c4065032480b01d800280c41c0b0300f001a807654201d020394020b810440070380310565195801203080b40002c8801a084c0c5941569003503103402c1c500b10f0303c4543c500203402140e000114420341030a40310142c3c80783c400507070642d800c2d00c0440344035640344001501d00d01d0f051209610395141d0308181c0c0d5417406200c0040c1000116003d00e014100c440e02c000381026400151540c8440c10b0a4030700e90001d11000011807440178a100071352400908640765aa03000400c0b8010085142c0c034103000b500141d0086400c002e21078624000b280410000c0c6200b1440395009280b410104141401540c5441c1d00c0540918180710b02c012001c05c940343c83d050401e1444107011520504500102d01600c184075281750407091a04004c64031918400101e881503200c5003814074107440700c2c001107820074012680d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 838926420 1250 838925170 838925173
    0x9010501020a1e0521090a1211040b030115080f010f0c200a0c1e050405010605070602031021060e0a02010c030302090f040f0204030b090c0f091e16021c02 68
    0x2d56450b0b200d01128101000f03014804171884084010301d00c807540640f54420065600d07011842011601c2c00101040c05031400b80040c6d14804d489a40e00c0c440c0118500419110310384074002c240360380e00c00758000c090042003500b5070000c23541e44509032901d4590381a850b8009500703003008440d69a501c4d0048030741400150761448000003000711898210203401a140c0c000e0f000341c01004000c80d40d0a5240c0c0040c00c242c900c0c5000c4036403144800c40c04810194070880c01941001c004000703407500141615801500184056580d503a14082c88441074819080000700390000c20b812081035260030744010300144500c03010030092100012255554a034180001d0020303501c0319500c400a07120790003034035500002408000d85110038600003070a40301e01e1600425481c0d801b141c1001401001041c02d60410058400fa0070000a00400308100e11110b1920074010351a040214078144e18400400d05806c014085444150419110103254004110144801403241110401640f040c500440145551540 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 838927670 1250 838926420 838926443
    0x51e0f01140d05030706020f041e1a070f0c0603050f10120212150408090f06030c04170709020d0b0f032d0a051501150c050d0c061b0305010509010501020a 68
    0x410042c000c101c000c1c00710792600090103440c00141c4107001800c810911048100d803240e00b48101540707450500b9070b8000214150f40f00400c004204120750f131002244665155603107031080d0400b001c080c10000f000a224440c3c1c1d080006402d980b56001c940a0700383e07040e0641d007544420521025000482c010040402d412030a107000516110b0b0000302030340c0300310050b544008600010343e1003e003400c49059440010011300805146020714140000ea40101c50306030450401040c00d0381d960049029000131481e0180c05016000001c000c0c180080000e58429036680000da02070754058020f00025074080c688003510308150785400300b940b07100300840951803a1003003000d040358079212070921096444e5010700315135403000c69030501600141c0044803505000d039501d40725100745540f4407998014208412110100000707000401c4204c00b9416920f0101c1b00c00354141418030080c5039501340001c0d5240074480a0768840e800d40c00043c100e07003040302e188107180e0341c48006980700c0203416402020418000c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 838928920 1250 838927670 838927709
    0xe0a0308030630060103020111150402040b06070807030915080103050a02101b1b0602120a2f100e011a0d0c120b190b01050301090203040303090501051e0f01 69
    0x2000064400d142019010744840410b0200c0d0f1600240c000d03000700c00d411140c01401035581103030290784240d481c03800620058901d10070112112102410080c23281b9240c0c520079801e6a039880c141c5403000d0b0801003c80e6501c00d24a800340410946200d4544c4204a110441032072078015034405048a4100b40600340c50170007542080070b4400c2d04c961440a1024242559400c0c4070900a2042c9030ba2081542c281515111075004880c403150b9408030301198460204c0c13940e4003c0d41d0040d244504120700300490620f0304c0e41410180c0100003400c11050348454200d490016a0024243c844001000c00400c0090b0401412509070342d0254000b0508007030007015001541010500c0b007460500038810003010075201c42115001d403209007026a141d01c106803c0c040421030510700c15110f411400c804000000c4490000f0340180014819092030071350110000b800d040c000c3d00408020369201000300540c0c80c2c00c000300c0c50250a000800400315100000048500c503004100c5816500d500303c505c5c4507ca80c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 838930170 1250 838928920 838928929
    0x4030806010503190c05070b0f040309050108070909020315040b010903020a0510021504140615010807120b0a06020f0d0815220509010b0f040519390e0a03080306 71
    0x182458030688a11800710800d12558816011700b65025036580796030b41c1841c01c0c1020308000160400d1180d4a516060000103a005088501180c01c00c2c20001c480c1d0350380c03100580e8000c450307030f00c40d429050000007001a0304000c401c5480c803212049908000d0000d01c10300446d102c50040c04001d41200d01c0d060188001c0c50050303856030071014284115042c612000c41030344a07940c070907103044510f01000240c0c06601d81092244a9200c4128545030124044c1c881c0005c0460002038050400d120384102c125000c180740d6080a00910b034064203146181365141c0009507544110b2008003101d0250b04a0307403c0c0c4074402d00300103000b00d038030024075211600620104000900b07580c0300740301850b1000d090048c200609000c0c0c2da11610469000190f0400d11509101040c01040283c501c0b980c0703414100300f00341701c10300040003a071800c0407000101c911207102400b070740104074505903480720645030110031090b00c0f1a41d1501d041031980d603510101034580c000d00800300710310301000707016482c1800003d009060 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 838931420 1250 838930170 838930177
    0x20c01110304052e0c0b070e120312041205041202061303020925080708040b0402120a060615031104030609110a080a140601050a120204060b040e010f0806040308060105 74
    0xc102901e10389540ca034006100d440c041c48030281c68601100407400c01c40300450015448602e80c0c10715009045e6907940d4500315120040655007071001e01e00c00e5451544a83d01d10034911310304074048960350708004110b00c444440440e01101d1940f00100d0040d5850b1081c400c0c1d4044030205406512184881d508125090f0002c004004021808100000c0580d03039001c40c850240388810400801402c55010081c1040d02054052083c4140c0e1000d0004095100d030006600c1504903600c0222600d03284005840790301200310146461240c50051001e01c00554401c10880b80300c1110f586100d4140c820580c20307100305003503505c0008800d00c010004500d250300121000d130311450b115500da10900001942c16121a0406555544840f1204082295184d0742880c070500d103a00070f0031913601d00b0000402c6035070140900f10003984400e54500071500c9e00d40005018141d0542070b903440b561107424002e000b990074403800300e800441d02d1001450010206c1c45600464040c0c0e20500341355203e40044d00d840e031 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 838932670 1250 838931420 838931447
    0xb190b0d0b0901110a0f26060405090109120513140321070203070609141207121106070506060a090507080f040f050f01021e0c06060f0a0305120318010b01020c01 71
    0x1500d483c590807240004400400d40e0140c0c5d600c400e03100514032803000f0030103004034800b1320710030452141034580f40500703a98440e07008030203c0e00415965623228030140500107041c0c0c0203100c3c04807e04443d40d15600f00e8007412012140c8411030100a980b9125481c0e0216803040054058201c2c800c855000d2030300c0d655920070110540203581c40c20b01e15902080c680400c65000c040011711200303060001e500d4420009400d0384044800d0081c10a40c0011952551010f1160f035040018010f814400c00241c0d45542c0d20103500105200d49904c441d080c640d40700c100403582144585814030000c03421500380d204080c011600d658601743c1d2a0f840c002442070181c03000d401668030201a00c900d00000e042000020072843c010400503031156902922041881c00d9000f504400d03e00a1003503600c0c0d0200081c005921800403103480e09040000000b0449507402e03a007001d0010700420440c450304032201e81c011805680030b216031b0a005980b071012139080340d401041a500503009400c1015466118298900886 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 838933920 1250 838932670 838932673
    0x152d030c090111030a090e0c090102120a020a021e030105061c0b0c04122609010212030705070210030603022b15110a0909060f030f080c0313030b190b0d0b09 69
    0x110000d00241d49540c20504101700011038084007032205081030b003411500601e04411722824110440300103901c40e644200ea1151103074020130a0040c9920810501250540207002c05070036a005c4181030203024019a6403900960800f80403601c181011041d481394000c025030300700007101540c1e480c140a80c13005441401205c2042c040032682007080c44000342c08522400700000303103e1030f00c8072141c400c81c01c202e88d22518181c2880000d1460344c010403100c200324070030910141d032a941c60a055840340a0804003a4001c3c00903001c00e00600d42560029007541d0003280e6841c07000030018181144042074000020050501c412100002000e0100d0400a01d6410102040700c0b8180801290107802c4820b4181c0000c2c443c1204000d6030301ca901c03071800034001a5040e801003a0650b16800c001c801249030040c001400040e40510098050007a90000100d01001e005038a50740d041c84c20780c026060300c0d0341030b452401015190011513180f26010020001900701e6002100700e440b00b1070054001410032205 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 838935170 1250 838933920 838933937
    0xd020405060f0a0e0a080304061808030c16050603011401030504030e130b0a0806070e0105070503120a0603061a0a0618090509030712230a020c152d030c0901 69
    0x341d079541025207110068658195190308500c0e1000340710700b2982995030302500311040e0900080c0c601100b10350984000e4202801c5242c40c03000010060180c03a800381c980e600010480705022540801d800801c0030360f50858010041c1c0325810048070744028401c400000d1110329a45003d075000381c0095070700a0082c1807212450086001056001180842c103c0843e1399401d40785c2200c0c41c003002c00ea4003815400d8010840c1d403070001c41c0604601103074403215050280100d01c80d000c00c0410012280714198402c1014501c1c1420b5090710b02409150108980c00350901d10007003510681110503142038940201580d00c943d00d001000d858110103006801200803001e90003142185483c01030074001c040c0c1000441c3d54085900301102c0e07520a500011040003a0041d0200c201e05c10b850f0202d44400810000c0c5964582c011000d070703c0c0400c4003001075000444200c014084d0540003000d401e14454181c0c1c218800703400740050202240004640c1c44519100f440800d07400c08800303002d0140508103041c250071 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 838936420 1250 838935170 838935179
    0x20301240c020d141b06071103190605060a050402070302120a03061a04210c0b0318010c1e0e010206040605060a081c091d06010f0306270e030412080d0204 68
    0xba5460442c425600c04c0d83c0c0d000103040030f000402504c1203100c8010808403071080300b8400250a44a00d80d8050480e61a6007001040341e9402c0c00860000000254030104a683c0c034034041018000444115104000c00030000800342081c1c000c44d0601ca81c51f0b80a0040004520b14282040c0c1042a2a800301581c4005c041440c200054203210f00030318449405864518000443d40d840175040d0203000b10303403e081021000284141182d9003a1880c0c09c001648950700d450810311111310200000c10383d582000d4404100a81041001121050002c1c008440c401500390503500950601e01840c0164041e02c0000c0c00f244951b8000c41d0840300c01405c000034165035460b03040c64404904502ca40c40030f5620368102c0389907000303c041e02c000c001268260184000d5440c40440421004081c5418401e10504d0440d03203a21076400300b405482070000201800b00b400c600f42086550080d000f482c05460300b030800c0c9400c140042510200c1c2d0040c3c0c0b810045100766628201c181c1c1068414a0b41d4a80034000400e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 838937670 1250 838936420 838936429
    0x20c03040303110c01050910050c0a02060d0504050d1806121103010b1c050c070f02040605120f071e0317130b09180103170a090f030b0f0901020301240c02 68
    0xc02540a41d0310f980c1151100c40407181400d130b4000303100b4140401001605400d44402480034039644060405c180c0744c2482240c400c2c10040e507110002e43c00080000c00404413412944a0785c092b40c001d1086840a01301c614040d10f0045078130600003000c41c4184410444c2d10720441e01952030f00d80110010401102ca0700300b0032035980081c3c00c42d4621030404940103106c04030501040b07081c104000401d02150525a0740207a4510488070054504100b03c80d018081d901c03180c0102c801040c01a000900c00c001450086d03841c7c80602c0755034040c80c0911600098a503034550404144014000740e001501c1f891a980d50403400058500843c415105000350b080c13041a42e00488020400200c10035070711069402000300c560076076522507500380210340061010032854440244c1c00b07020040081c0da00c0244010540d892040d9610440c40002d400c01c0110400c203079066401d0180498a80c410b406803200f4428070b00f40c3c0024000d444540107003013100d40c1034920b004c50058009800c1c2c00c0c1440081c16680114 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 838938920 1250 838937670 838937677
    0x20618190503090907021f09110a0312030b060306030c09041a010f2111010e040b04051e0f0708040609170c0a1e0803062e0206011401050f120901020c03 67
    0x40c1c40540000c0348200c02e0f4106035484a6000107544054004109030031140c051542824144c00074182d511314502c4100040f0b5900d120506800030803402c0f01543d0391030480c002d03241d030b020030708002410442040700c18101001901d000345d00080180c026580795205100d075400008000717592590351f601581c51907a80f0400168003901401400320f21050030140e002c15103d824510861034074030303004103c00206440f68070000903030380300b40380601d107900050000ed805045441145603010f03262401344039036424020a01d034030641c1c408400c50515503604507440c880603801ca40000c0460100700c002000502036520020182e48074000c5000400b805078420000da820540c2080170303540c001c10741c0d40c041c010341c5100d01e00e2a4008242e2106541d0746503580c00d405000181c0318a0107180c0c0280c1c00321740625501a0100002d0503180c402e40d8110038688000e40e034901c280314079029540c0402c001011540b0400407948030171944940241303004e01c1c403600c18800030303001010304507155400d000848071000c090000f03 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 838940170 1250 838938920 838938923
    0x1b0807060527010b0108011223160b25020105030408071b0e07020708122b140103120306060f0c0507030b1305010f051e04150908031801050702061819 66
    0x4c0880001300054000383c0306800c03408091a20020a00004904008100028003104420140c180f409110a8078122b911860110240d10310f49001ca68000c00700050310b50140210740d011444a65803201d130282500f0000d001c3c1c0096410000100401c505d840248001881140805480f4102044403010202d50f50040c4070480040001d00010f5541042914042d1030450701400345408c1c0500902030350310038090a0003400344420f0107801054105000070050070420039003800416094950288806c200740412503a0b000200418500c99209106900681d40e5a40702c50340d051b15056019105483c5c40f6a080b50240310f00700020000030517102072940545182e440141e9041818139105080d80c0c4044000103141c1d103028100030350800489481140f041a498480049481710308241e040840f642540c2c031400da0030006200100101c000084d8403454046401c0004200803840003401d1703a00549070600142e00000100702822280011003010345108001c40c0d0400d000c0750610310415441010 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 838941420 1250 838940170 838940173
    0x111030702010509072301090806010b091002060906270d020c03010c14040306020307021203151804020f1e0d06050907080a170f0c1b011b0807060527 66
    0xc0c00485902400b4041e0030a030440040c5c00f509080c100399040f0705c8050301255503400100c00d81c501240c0d02642d03a510240c200d100c1900d03119a1190303401401688400344080c0610000c404688450303102003a498004d180c0b540c0603104607101d95482014094020070240f49407621203402e245082010407610718003443c00d401401a2181c1401018210741380122084c0078020b03028490b00e411100e00045805480c1e001d10700586070307140d840003285006194030700c0ca0503c02d000000c1c810348250503412000b241d0f400f00c42c107805022039000c2c2030b00742c16401c2d103009402904032170300240d80780380003040d00e40080b002c180c5207100440380000055043c150341740140d44455a40c800d10030130000510a140142030b10300c0c010100241d0540e66007440d5401900049140440442e020010202e0101120400d2070500112007029440c083c0c5941e0b104581c2c8020f81c04141c042c1c4480082c01d46036041c1924132500840c103e4241140f5489040140000504108542200c02d00446d0300031100c1c0490302c81c201d0200d0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 838942670 1250 838941420 838941427
    0x100c0311120a06120807120c120215150303070609080c0102040e0a1401030512070303090206190801050307060e061c0e030d0b01020102030c2209062904030206040e04080c0111 77
    0x28000c0044802642103140b180ba0130620541c0850030003c222602c00e50701c19500a0343c03070b1100c01c0032a408401284000c280c1c0380c1300d503e5612800d074002080e01c60400c0120180042e034444c00111a423108100007802d0701608148502e1002c82c006a0100794541e00600034145481283c110003401c990043e00702c48540280340d014084403602900c1400400350b642c60591030154155203540b661840d0405180d00c5d2008000340341d004140c400c0e001408800e60103000c007a1a10207034040042c0c0040b12944800024145800004107407a0000d1120101d42068883e040000c180400f4032100d0350005024850001a25000e0030004240344202888220158040e54881e5100d900d07107400d0b00d405510003411607005100b0701102a400c01c044480d13405044200c80e0801c821100300380c810500c0c1c0d5000000551801100069402c000b079000616400305008040032100c03103221000882c084c500001c2c3d0482000e11041c00509540070303040750800e010f99900c0e4140501c02c00c2850a4440382060410400c0e0080b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 838943920 1250 838942670 838942681
    0x9030c0106080a0b0f0a060801060603020706050f0f1f080a1406070c020a05040b030a0605090f160f0303051c180213050f0402040f020c071403070b0c100c031112 71
    0x80c07042101404a900c05803098041c0b40d1104400e04001504c03000c0d540e1458400310310010031a84c0034400501401300280075440c2e9801d0081e0094100c0b030350544456040c0300000e02152080500d0074070461180072407290b40d4948078100c48180710b00e02c125012040103401c001c0fa10190400c845007017148103024a6240f05291800b1509080c0050007180501c0141c1103513030300503035442d0035a400b9208180c40018000f95680c00003894422a0324014203424a090244402d6420100307041c1d02d8889034004803400070301d40c3c01d00c02c1034640ea14401d1002c1080c52505c1440082d204000401a2410719079081d1070400304040b030081140c0d00c10704c600d100c00c0d60100003d4214100302c0c06c004000d5204260410207440e18010f14540c0741c4004000900c46c030f81c0c451120104104603810f4030707607100190b01114a140c0d00c64060b40c001c1010b44000910a104a0750000307444200b4100f142c81c1480548050700d05510b125011102410100703103018107158840c5d00c05090010b5503c0a46080c0740a40d0045071a420107 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 838945170 1250 838943920 838943923
    0xa05120108060921030402271e011208030414010617030c010b0f130f060b34020109090903020c0919050a0e070b390105101a0c010e030309030c 63
    0x11041303049040c1e0b48030521104081c0f092081e40e60298054441400c18142d0001c0c00e611324031000c001e02d003540c08103020310404210506060600c80c84070a50102640d0326080e0440c0d0340c05280300014005081000000d00242c0708442c94841181070500122b85a9104c8085881c1502258103810302070f48013242ca5000322a0034000c50300c030042c09590400072104d41c00c010500010404048407052900c95040f00742810082c0d0190008000c8001015120195480120703841d119454040f2034280d03280840400b0055007000c844500b03a41615034681d060b21700f040e12030107070107168420b50079800303403142c00d240548515001e1071190350030782c1040504544c034005407401c80e01c0c00380102c04142d18080019100e81800240c07075040d101c18480e00303501c9042d01e01003124600107000d51900010606501c8270030072040d81ea01c1010500742a80203100541d41c55800b0b20103881c0c1c1c0e204184516241e00d80c21500107540710001c1400c07020075800440c9540b50b1035401c6241d40c3c010348450b4003580c00050305401c81e040 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 838946420 1250 838945170 838945183
    0x71713030309050304051008220c03080715050118050a061d04150c030207120f1d0f030a0c0f0e0907051c0b0709060f02120a0e030708071d061f050a051201080609 71
    0x29840a401c27181495483e68503840d601800020400c0000140b8081405200c1d68280050480040180a03541c1c55038100d288000b00070340585a00d505040105d070440c034003805140d0517940e1101c140d00e0440019100c4121115000d8001d86a610081149401c4060f0f24010303014000c0c0141c03000340e5660014a025142d0f51500d10700401004400b01b801006264000b0b08002c8400d00b000d81c20707070480c015100007203480b04502c0314540c5c5840350307980c52002c012000c5190070485211201c0f009401e60b0b2600000c08899049807500a0f54001c00b03001e02242c03801c210b07000380c0a01d200c100b05d8450000f030b6580000031403003524110b0126106200c1040221f9010f01c005030070002c02c1c800781000c0415044901c5581c0a40f0140b001404203189440e8150b803000c2000318010f040e044100c030b00703040c0d940400d00304880002c101c28100729612000900c1c141070180886901c030b0002420f011000070203500407510360700000520700c200007081041c1d008807120318264902034100c41001d00303290700b44902164600711 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 838947670 1250 838946420 838946461
    0x90606020f0c060f0c0703030905210c090a1401080a0507121a07050918090f010908040e04051906020a0e180403030504060f06180b01020c01020d1103071a071713030309050304051008 80
    0x107081d5580811a148007151040d0ce102d0140c4078403e041c1c0700d454071140a814841840b10890100f00000240e1320400580c180030940240b042c0d83d401515520f20302d4000c0880c3d100501902c0d094000c019100d00702074032941d801500c5250803414a0041000a01403500ba00b84850b451403001c0d081c445118020301c07404c95510180710003080716014036034402c4907a00480c03082412002040340090203128090103000305210300582503100070301c101d1624030300035045810508005024152944034a0410524140368445d0701c00840038281d4071035030300b00c0c041d00b8010811030761603440d440f008021a0072805000c0c05801c0c41d000700520941543c100f5011a402488154119070010f0820003031660041040158071225242070700e880200d68240074510f10482c1e80040002c3d0412241424203c0a4000980540d0380b0760394042500310303c400c03869141c1c003007503c00e07a0212822000e81400280030398800502c0314880c10590341023582c0c5030002000c040c002c0c80c0703007404100c0090030070901c034101505400000d03 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 838948920 1250 838947670 838947709
    0x12030f02180d051216030f080c0403140c030f07062c10020c031603050d020645070e0a110304030f02160f090606020f0c060f0c0703030905 61
    0xe03000001611111030381881c014041e203200d2415009008040c050401003000c040340e4a5500d407030a2040d0b14081801000a6000910850050708618415400c290080303c1d0700594601742401d5403101007010016072008170240c8100040700c50252014003100440700c01c8000a445850725008001d4514203581c01d2501d504003134020a200e20f8404204a05142d500540301c0800340c4018090507403a100c06030032115490310038813400c00c1c080046001400166442442941d0601d0810300f420307030751244161201400c40303001305400d14a8007200c0c4102100c6d42c000313031640040f130042c40c040c0e200301c0c80d040741c44007080d41c00404050091401c1081c8403900015030399404c2040e100000010491030001600040c204080480310210340d910800400350742e042c1d54515604801c0d514030b070132802c0c0507140c403800e01d00c1c0d0300303014000400034004a44c11231480da0040141107902d180030200500ca038004a0481c510010038041c844400c9410410040514400d03100d61084d0f078140780c00c02074882c00445890404 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 838950170 1250 838948920 838948927
    0x60f090512150601020a0b09060a110a08040b060303131805010b0406140310030218090c01020c031c0c08040b0a1716030509100207050a02210d05030a06050d12030f02 73
    0x15000001e84005840b40c01040400141c40d0f190040b802c0c802c2450029061110400503c003c006000c216280075000ca88410407405040400c2010240039018002010449400000d0049400c14284561021000b0240c0b440d10004d84d407205541d0304140c03c201d0500d5140070303410111a8003031050a026150403040d5505042c50080300130702034201c20401e0001c041e0088003048004024032a0f640185500520300b5400e00c1f021000d182c0007900440b20284588155039041c405940003084102104101074003600032000e080b0322400354140052a40d07010040710005040100341c8003000b8001400210340390607990419190001c28603004181d048120030b649006202d4001c6030b124542080080f0f40c1401f0905030340da103480078144400c1303019102c403c2d8000124202000f002280301c16829100711400d000d85032443c1c5690f0782e583d42410420490354003550581c06428011030146520000186011500d80d860303902145032117078400780880d20b07a941c607143c7d02c07841c40d054003030501500f1400a0441c01c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 838951420 1250 838950170 838950199
    0x170307080a031e0e0f010506010e0f041a0904050706080f0c0d0b030705040c090306050c03010806221a01050103140603061801090c0308030108060108030c0a060c0c0c060f0905 77
    0x4a1140381007100c1070680c0d503560b0201a00d6070110700c05102030300810400242c6007500c2195110b29203441c000d1200d503c0c20002901d1076004100281400f1070140c0680360350580c1d10103001c018082643c07000840d410b046065015941c81802c49449544076801400d941e0345007a4001e0240c1001070049021458130904001080d01100282c50341c80e4040038000c5082c1d03c030000405e0412100741c0105400605100ca0000305a412181c00c40c202c900c5650100110303924028440110b004c2805205515044000030030369200c54444600220080a8402600c0c0c145a03500c840c1101842c100c0b01c401004000b004114940c0c15124030910b085030700d0452142403821900007070f01c4a100401762010040d8008610140d0482503002c0c2c3d002c3c0743c1c4132103810269a22420a03c0154009105034a20382c0708035800854a5000401a074580e102d44c04001d000007180c56403404064005090028204180d0b14504e03030204500e100200002c00d46a11404189451624010810f600da40c01040c000c0c4050408443d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 838952670 1250 838951420 838951433
    0xb070b0901112b0e160501020c0f040b1206130308090a0b01170f0303090102040306110c03030430030c0e010f050409020706020412050f0709050c09040c02030d090b01170307 76
    0xa021030081c0c0d0a051400480001c86011060191620f141551900300c107208955800182840841c040c05e511008083d510001241e65410b50f482d400d412001085200750241880c0e000311661100041a46254242114001e03280c00c01c1101c4c0505041040855101415009151240c0012030280a0300501541c0d48800c0d450710010b00c10540458034480c1044001d46007402001804c00d030200c1580d5981c10311004c254040c0d001808150f80c500e103008404501c803565201200c0c441040c01d0069805d6075225240d0400800d842c41d0640c5102c3c656460207040d25070300806512600c540e94800240c41c2e038060200500540803c801ca5051040301c3d151150385503004420346003202d0801e9009039481d03c0501c0d0480107401154401c50a03071843c7c0d00b10008004c00460640c000d502e0704d00031030b040c03281d03a00604425144180c03581814800c08020003002030a0603040303400300ca0102d004032441d2610481030304049802c5c2c20801d8035260381e03106c010702100c1c0719600000b20b110543c00042d03042802c0c549800c03 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 838953920 1250 838952670 838952677
    0x906060c110f031606080108060a0e1005070302040306050a050a0f0e150603011517010507140307050d0603020913020f0a14060a030908030a0915060b091c08040b070b090111 76
    0x910805540764181d45aaa0030014140c82120100039800d4103a50303200d001c6d1194100380a005010300940c1c001400700c080c21f104a41102d03040300d000b0420b200e1754100c004020030001d082ca0007010740070400400414224012030740512071413440044c19280058510044580071003080d8000e500300380c03031010510030010704500c0801c9040040d1680c0d440e075100090040900ca8424003d080b184100050040341860501c0f4207030106000a004907940d90100315075050140100321015502400490300c07040c071420203010404114040018043d071260006410104100e07481ca075450103041d0000b086040c9406c20070655101590074080d0f107410101010040d44d0b811285601031039011aa80d10341381d104e80c004110b800e0b04040034a40e80d05045101c1c40183c4a1000d040d034181f40c088001f56031154092007020111210420b03807904241981040104032854504049407400022800c1c2d00800c1d0300800030710003448981035059840031585480c130307501600146080d00f00c0c1d250904000d01ca07031000040703 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 838955170 1250 838953920 838953953
    0x140127030515072303070f1101052a0705150a020c0f0c0f1f2d0201050a060e19020d110d06030606050d0b0c162009060d021503090307020d06060906060c 67
    0x560307414511f01000c41e00840e20701380d030949075820001800f205282c15220240380c1c80c0c00c5210100541094026078081d03105002c4000c110307620400140e10603002218200e80c0218140d8805441d00703400000c100e28102c0303c00d01c000f4942e04030100d108500d01d4691700307031010180b098030200d00031032000c043d01c05615045030044007800082840b1001c0002000240c01140713841c2c00ea6246045156074000303000380310480c4c000c144a03150000215116a0000c0c001e1310410b00fa00843c421410703101c0450f006504001184103902e9280e210b46100620b051005d00708070401da4000285d82c034614180141541c0c2964000c0d80964001c1c00703944007061851704c8a551103910804201d0780d4120030700100c10303510a00700000d403000d00b6050328400440e04882003140c1e4010122945511a29440c00308540101040d2000b980310701d8810720361600c076552030080c0d940040001c0c103880c2810380e90f402044690012607421644141e59810901501c005482540301a02c090314041c0c2c01c10740140d681c7d4030b078465003407003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 838956420 1250 838955170 838955177
    0x10e0f070501021f1d030f090f060903030711130612150605030706032f0d0f02030601050a032c1c0302090a050f041514030714012703051507230307 65
    0x1455416240607080802107404004a036615141c0c0030007c042c07a0413001d01140303d8140c4d100c04030101d02d4408296113070303e200103001c1c626002440c0c2e41d9011102181c0c10503a04265041d5100d0b2074a541c51003281d0007000e0501100d414914580b230800280b500c00d007040c2948a240c20001c2c05940c4001656900380c0e441b604000800c42c01000d41c1d40601985d01a02c51104018244103903115021000542190700c1403807018801250703484105426030008441a031b00250003803002050b054840e400075202341003560301d04402688041a010400d00554170200a83d81c491918681881c480310501c0124000c01e140450400f4110000101406600d01c03805204a003d10480c20255490b43c0c04100e801000d528192101e40d5220b00e94400901007103400740c880d005207940001d00783c0841602144180c0c0583d18009204029520900032282060002150302ea4600000c4001142000000e03000d800c02c1a44000b20300d0154402459581c0d64001050949407104100020715032040a03280c00601c02d04 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 838957670 1250 838956420 838956431
    0x80d121b203a0201060302060a0e0a0b032706090606040e031201090f06060314040b04051f020d1b080705030601021002161119051c05010e0f070501021f 67
    0x1c4a05150a4030308608140102d08007079030218600b00c201c0041c61a51070390b001100b110111001c2039003280d00134072010350880c5003004450700052007060959050440240320220380781d01c0c0c0d103510103103410442d04040d62200d90201070110030480c1e5a840108685000103080a103801d1240640f902009080d07140620b84448030440c0e0300c041441a5010a18190550041985d581caa42805002800c0403445054a810404101c036031181c0250181d912018000f50016221079942140300c03607008100356568040c884078075020b507903412001c0308800545c00c00903071240047c0140c241100c00d1b005075085171f0211a0304c2c010003150000020765214017103080c550307180e82c0c41600503801c00700c81c42c50004000f80b000803447d10760106080c1421040740107003c00303980e1b04282c409201e10500c8820030b0b000650300b0740808000a01c3c110a00c544000000607844040b000a580d0322800e40c1d040300d0035105190003210760046003800400c80000108802d10060a07c54051141280c0b030a00032403828003032a0711780 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 838958920 1250 838957670 838957727
    0xa080321060a05100207150e0306010314190803150a0315090c05032d1603110102030d0617010b0301051e0405030f12010f0603020a050301050613080d121b 68
    0x740300000c01003c02a1407244001c51400d0001d40724002801401c00c41503040c01041c1c40507114518400690300050014422642103445000d0100c0e142070040303d0911503409142c20a002201d981d040701c510444c0125201d0910021071007140100c0c3c461a40a2045800e0420200344081c41280340d5800c407200002c0c45020f0f03428544178201c5030f07403c859054440c40c1d002600420005c00301154100401c1d041c0030584280728601038481c83d0028ac00d10000d2508802400818644000c3c03400001c0b050044914010303082e06d00300d082e140540d10114502d4410030403000d01c0c1d0030a024030103807101e00301d00800403860a038804284241001c2c1e2a020030f2a400e10000b4104a4100100c81d40b180400d0b9002d1b0315501c8144680b09029000d0203401006540c4440c0040c0c5180a4000c0d0b808000c1292141070a603800c00301484401d420007400b0350014007180d00d000400b500140a0103110040c8c0707039116000450001c1c0f115065400b80c0c284100035624410030140d51640c40110310040c1440c0145408500550 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 838960170 1250 838958920 838958929
    0x2090c030415020301120302071d070f050c061005100f050f0d0b03060f010302150906040b0a020309130515062d0d1b170f070f090f140a08032106 64
    0x20740d84084182d0710010021600c0c00000c03407103a88041c400e50842d010b094440c40c807450301348114103440345041c1d0b0810100310000d0140d80403045800711440d00504214220901d41d1030400255040740b000041c400f403c2c00700b030500c9200300c21036034164140035100c081c0c0504001c10303902ca108411001150f0110f0061341c03011080d0800f194083c0024110b8005041c0b04041404505083c40100d02c11090400300c80409124a000e03a50348210041c021401c0c14941410340f885a440142d1100840c00108410102c80c0d032a031810380b09440804a000956103030401500c5000d20540f40681c0c440c140a20480d8480c081002d41c0c041e4a00508040e00341c06181621040c0c0c4034040e10184c2c03030a550030304503126040042005a01d07510480c079500e01804841c01070001c5840c0c20240d071041100902d03e80001c10170790180700300100826507803509600342caa035604403452201543c0c000c400c001c031040e03000f100c1c01d10b400c2003804050300301040514078142c0788c0380042d810070040c0d480890121000500040300790381e5 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 838961420 1250 838960170 838960193
    0x5130801060b0408010510080d1812030306080708030408031902011812020c181f0f140f180f0a090f050c09091c050309100c0804030e03010902090c0304 67
    0x518000344002502d456500ca001d80003402020300070361814000030805010f008031002281d14040180600303400d2480c0840325086a07100044284c0284080013904000102c601c940082c003d50b0700180711410074400c142010802d1344098040e600038001402072000100440b6801e0240190702070628400f060240c1c0036080d180e401100c0046e49840c62000c2c00481240028800c0c5940d00340c4c1c0b81c1c90421010001101d0901c8405007903941c0100010b40844000c2203c503d82e8217510fa600c20b006695940b0641c0d1403c5907030450710940c0b01c003007a200480e041003e8502c00001c01258000440641400500850400203024030039207030700040881c40061700c40c0c0c480100745802801d5107091498078184550340310040b0402d00e001d529018005000001c001c84c0d050003000c00c41c03114040b01550150120740340d070006016500030740642c08210f01c054680b0300c500c1400031269140c6a00c5c17880c050030081c0110f240211100e009074180148100184e0300c045080c3ea12003030540390340e0b40745d0300d880c1480614000c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 838962670 1250 838961420 838961429
    0xa05010b0906030c37090c02010204120f1a07020a0506250503070509030d0507030e09090c220204030605091e1c031803390201030c050c0a0b0403080f070804030513 72
    0x45440c5d512400500c0c0d000041400d4824184d41880240d5504501b2402c03407103944942000000e41280701030000383d0143d0050582d038000e1032003152803024811192941d94040d101074001d60310883d420030403c001806102d501080c1c001c4000d0b00b0101442e43c1c045240009080103082140c00000a0312060140c800d40b1203804c030203401c55100160348a0701606913804170380c0a034041614a0103c48091070422450fa10808020024044650640e014400540080080c520007042c3e10311b0418050f082074405000114055500841c42c2d0070110850303400c0c041c103014108000303468440c2403840c0c170a000645250481c401c140ca406450b090709011030041110391000848240340280c910140342d032090650502c803409812a11080810303148903034010100516101d50318a0707558500001d9030082e44541e20209050a20310328040d4440165400c00d50704903021a044038018091005044e84142e43c81d1741700015465a8490742030008000e01a510f0080c030080030400c0c00035445602e407903240c00341d00080 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 838963920 1250 838962670 838962739
    0x9150a091a0a080603030a020a110a05060310060f0804050309010f0509120609060709030b0606030402010c0f29070e130e010e01091b1d0406090b090a05010b0906030c 73
    0x10025081c80208560011411000181584001c0368407072902000b21010350000b03030001d1201081c07550700e50070850300c0c94031442e62103041d04000044684488000b1485552000d0010b00c1c1142000d60103024003486802040802c44070a00b0000001d2001040700e04107242420314180c40054400d049a0f50b124000b003140c0c000e800140355031422000062050301940001c0e0036502c0c01d0796800d601b2a0b0412603440302030001300d4400041031960414000846c0c100d80189804004142d40da02c4201c2c240d810782c0021034408900d469200c2500e61251009000d45070010704240b21400e011000403d0540e0340c0401903c18442d581c264a030a07403d9610402540c101240240908408000f0260003024022415aa00a062003110101032071a6140b482901c081d41d00891001e25000325042403880020f104480060761032007004040751403d2241485118218000c0c0000302251a00304d081d50300041c10180299400410310a560744c0110b820214400103480030f401d264000c00001648180320802d041d6030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 838965170 1250 838963920 838963949
    0xf09020d03020610051005071b090e0a051005010b0904020d1401080703030e03160e0718091d0c150a02070504060e0412080c0304060e030c100506041109150a09 70
    0x100742e00850b00341c1c4141840c0d015000515552400e1003050403800030690001003003001a034000506042582100742c1200c0c040c0d0070140c0e1030f554107400312401e9072102007195014500340000c1060800080c00401c1c0e440f0300511940d4034001305030380729000d0b60390420711464002c180300c0d20b440403562040300c41540f0814000c01d40d5960700d291903141c07801400305800190360909905801d0400140c04d420504070103240304802031812402c80b401c4d1802030520010040050380c0500842c100c00b0081c0c000c2d140a001c0000d1912540c00f0320985503c12402009071500284d031121138650798000810310102c1c08001280d901e8101c2503040f801c00e25540c0016a1003071500401050f1800800c000c2840380d4802d0700d06200f1040d03518410b64141c40f0440c1c1c6000a4401040014002480c9030400382180b001801102c2c241140c20381e0320b900f080e5101848005d816903a0b07081005e00c0c07906008101d016210b10b0f9006d4a00b40c445e0340861003440c241c100749401c001c000103606c1c0300a032081c40c00100030003001c0012102c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 838966420 1250 838965170 838965173
    0x110310150c0507031203450206030a0b0105130b040501030e1f02090409020904120206060d171b060a09060f06081b03070f080105060301050f130b0405120d0f150b07060f09020d 77
    0xb036503001c0d4606500040c204090b202403040c1c032420803447c2250014455811a56400c40b10000b51502442c0541007260600000c4e414089190410020303248a29115460f81d003884001002c6412091072019268801c082e10b9418900b5504103c1000c10034440c0940e40308a0300703001c41c01900c05d00340c00030341010781c1c40200000d00960140341c0480029541c02c0e1030158841d01d0800c03000d1800c091015081011019030488182c2c2000010162009030800512410850b2280a41480341c02c0303815203c1c560301d80f02801c0401c03203144181848500720020800155050a480c01d645241001d01c01001c0c0800c04040685a40d040111800402c01c0034100b8140030b031900111800b030081a660540030b582040701291001c141013010030310402c9050340d1040788400076101d1440120016000356518000c0c5240440362881c6207005101c0001d9201d00450714015520780c00c1c0455405003c481594049a8414040e2015140c21500c1d00d903088000458080000c2d00c44400804803c10300960000900c1c05650 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 838967670 1250 838966420 838966481
    0x90f010f21150308031902040312050c120c1606050a0e060d02090d240603030e01050315100e0922020d1b030c05120d0819110310150c0507031203 64
    0x51048202110b000c50f408488806d0f00b080e40100d02009068030142014024120300ca140502103901c004c500302c07440c0c41c401c15000803090307210030742c0d07402541c001c0c04500c030031012010040d00040c100c51501e10301e46065400b0090200c02c041c0da1085c42a00e001808605160080e01901c0c118200144074074804516850250030400a9a040c0c52a4403161418404002d469214100440350151a20444d040050f001100c582c0e00081042543c14110403840c0240d440e4405a0070000801c0d8a4600d0004009010440c00700c80082c4039034482007141c0c1000742885c2500035030601c0301781d0584558240c000c041c500f00701c2c1c554024454030306540a020002044c80070ac03d1690f011600140c3d4040800011101e420362500908240200030500b850301040f544002c2800c540c40c43d0602c41400100719000c0180c2200320f510549510510018104040c000c0603203810f0000483c1026081004050100b40d6800392219901d200107000500c0040101502c039020381c00181088444147e20001600c01000c00c8 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 838968920 1250 838967670 838967677
    0xc020c0915100c02040f0c0909240e090f0115061209030207031403070b1e0717010b1308010203040501090c270207080c030a05090f010f21150308 64
    0x5600c24200d010215529180e1070040e242280d1026001c1c0803800165401900d440101079400c07038005036a020151800e28492184070303140010741d940c4540243c903100c050016504003000b0014016115007014908104a02c17132541110b441c1000e6964540e00c0004050402c03203c05032000c6c0e954200a40c510054041c054090300380c1310b003a107812800c0c0c2e2140720080216841004010056884000148040380d101e102005401100070210791070200690b03034680c4c1040042d11651a01d0312030a0000b4014800001002d602100a00d0300a01c80440c864111403448418440c0303e0302d1600c0000d904014040942e5200043c1900300001d541d2810685005070080c00528000d0701d00d0f410301100031907041c0003440c0710320903000c014411080d0101e42489034802548030b50f00032213044008106107000c1c0403081c006080b2884071602c40d42e440d1684d00051001890910303100da030412400b074543c0714406070807045803201101069045000f102d980f504040c001e00a44080201680c8080f000008100005004 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 838970170 1250 838968920 838968943
    0x2907080106021e06190609020c0a06230118090618050f120f0c0304050901180509150a240902040906080c06070201050f2b0c0e010f0318060c02 63
    0x229298045800c0d10001c640c0f14111604a144d0809004030b000542030259400a88010201c0001d8140da9034035650b049a01c001000941500003c07699400d125661081d42c0f01c1e061880318990317000621203404080c3c190305004049003c80384030802c078804c4129030f102c0001181e0001c01003100107110515084454002c2c4e0080310181b0810b0030b00c00d1810004912800c0e640c801048041c2040a10740018680d07070807200116a40d44012301c0b0004840d0f41d14244580281481c180c460711008000015200791400140101290b60142440d40082c5000400c4113a0003031503850700160344d1a219011030720140146151480e245d00117080801c0c40740255005000302d40b980242004280c2c2c1e0391005a440e11050018168401400e00c00000594000c0c402401c0900701c1280340340c909854100907100703400129101030040e10003000280c0d8050144d00c102129a290f40c14101c2101004000013040482e507034142d03000305610740c0218007500340c00106412255500640c107020003003001c1e800950f280d54130f010 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 838971420 1250 838970170 838970173
    0x1018120c0305100b010e0f03030705011d1615081e041b080109020d06090c0b0a030b040e0a020a15020a0501050f04060b12030f030c1606061a1204290708010602 70
    0x900440e18020381303d4841c2c0141c040e151648030602c1901040071610141d640c45402d400108181d0000500238480c2c800100c00d0056a000e884188580b0107113440c0b00c122511010401000c1c060010000f40345015801352240c2c0ba101200b6a10b608801124544541207104011000c4041c0010003001011501240c13660303d036002040f40c0e590454a00382c90701a01c000c0c0d0440d29219139400414003980160412074050b1240390301583e500d01c0d07046134640c844c10780032002960700c0c82c41c60243d01d0031b4003031040341040020007004640d0385030f0000340041901c0d115100d0f042c09070700580c49071180240b0049201a42042c0200202c2c0380851b00c40724560710440381160310f507290002100c00b07460003403855108800b24000450030079102e0003058810754800f078060381d424001400078034a10300c2d20b0035183d00d00d6403103070740c011809030318041d29040601c41c2c0c0100303001c402d0414040d400380328041890955019401c501b600441d2104158142d1001d2032024820b00c10680788001c0200e4540c1013815107040740e00550 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 838972670 1250 838971420 838971433
    0x10504050a1b140f0111070e0a050109061521020a0306080609120d02070f0f050f01110a0c260f0421082b050108160f03021018120c0305 60
    0x42c0c51540207205020b141d50240c8203000d00710181c10a081510b10616041c1854100c2d858600c4640b481d101d1294801c00004031400e0802028158030f0088600402c0e40380818000a800e00500d000ea6607030350041c0e80104480b290a40f203151a840d41e4002c080b00c4044011903840707984940c002c4c05000c0380c0c0542d41c841c4c406c50380450b410b0400084d0b020100d003a115405400c5c060f41c0212040694030280c416106080c03003944000100f5078141448089a00c070360300816015000c8041d03282510b1102000640c0c2c040d013032002a4035140c001280082ca2603102c01000f11080c650681c900c0003071a01c581002e0b1541e0301080d03c1c8804140c03c00104155400e02008520048500824030040091000c000340b4101d414490540400c180c0d458110240512030a000c0303804c000400c581040b0340d026400301044e540103640000d89100d200c00c819000d485450302521035241150081840361091700c056004100148544e03c18807110480004013405400403000b0100c132541c01d09002061030b1303001c103036018000d60 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 838973920 1250 838972670 838972703
    0xc030d15140114040b0a0804200a051311030a060528050d05030903010c021b06040e0f06010912122a061e0f0504110a060203090609040e010504050a 65
    0x3a60300884801500e24078070410030000440701001c490300d103003043c11400d11012484440031030151201703003481e03a503001c610325007402e146048400840c0b121080c10500401c03c50651590150142650020380f2034140949030713540e900b801882c03580351101c01c000c3d010040c4641d8002540091046400c1111440b0000c00c2c03041c01c0e04025000218185000c0040500030045810b050300b054640c0b40c051400c0e00e09000025001c01c0c00c0d14042102600160003650107110f94004a4130702141e03c2900b074492038202070901044c2c01d40e4140c0500007000308605600055110382c071690080019003494003e460801c2d030b517440e1109450000208070000300300483d18030001441411000900c0110140c84003030744140a0315144006d1920561015200c404207646000710403060041c0049141881000601032030300f800c1088607407025031903d85c8640240b8504214042c3d00005031390f542c0c03808548041d92000540300040041c054021295080c0d42000c0400c000e100c404100d0040141c05008410b800d481030307 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 838975170 1250 838973920 838973951
    0x70801081203160c020409060e060109020f030612010605060708040614031e06031002071a0a020c101109121c1103220519061d090f13080c030d 63
    0x3450806a481d61040c80001c075840e4150300c1c1803901c90501d08044103d032500fa0003003420386814031429a440740e01d68030400d203030850812025004103d43c0d1002c60400f02d449115150912024003c1d600c1000217882c0600000400e51200b030060000401240c0d03545018500031a03181c01500c54074001c00c110400b100705404884040f00c0c403511514410600c80d01140c828400314203409400c00e90103100c2c668080031007510382d1004141042c050340f0300046020646030902e03110900204010310041c01403040f401422400900308582407002c08002c58802404896203d00303014064030298401042c078003050039448049400010144280d0b00c080744820054000c1d104070800a0100b00154010403160111041c00155400015420603041102e070f5910030005d410b200014014101d16900c441d01000400e8100d0b642d050041d042140c08030f25050310b08009540404000e2801d10790b20350350000039040101c090042c40c406548400c0294031802c80e03262544d500c0c0c1020107454612480d0403002d100400f032 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 838976420 1250 838975170 838975183
    0x9010606080105010c030c050c0a09140c0909180f01150905060a06081603060906090203013204020315100206180a230a080304080d050604291305090607080108 70
    0x3c1078460000c80720b01030b0350840d190a49030701c00756024010301240e407003550340b1601c0b0380005040c0500d01240141c1c3c0d030014101d86032406444a094400e080000b000192504d034800741c1d01000b10b040e000350310174490780c0041c10310350a403091020b59480d10a16400d83c002c510540705c1a11a1711070b040102d90b403202e06005110409002d40c001040119000034404064086024054503c514011072450f076034501c01e00039903225420140742c1ca50084014000021100d9090ba03802040d458805c1d1103d00030303c00e0012031400491501e00a80e00080003404140460360400301c900409030240c00098183c80000791900001c0d00c001c50080300049140c800c450b40008d4030443c554121110f114405001c1804550b83d52040d480d001c2140642428040421110006148940e0040c1165542c60801144003004c4410003060244140d180158800400070340480d02d030101000c004c10f08403011002c20000c0c00c10115003c1e00c5450506180030400d801c0404a810341c020301d42030f120b403000d50740c803141c0d02d645551 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 838977670 1250 838976420 838976429
    0x70b0a0801090e030903120309120721050a09031b0e100906140325050d120917030702040507122901031b0e0d0b0702061504020c1207110d0b090106060801 68
    0x1402003180c004c0e11f400c00c0c002590415120300c1102c180718604141a0300e80d810880054036404e0b01d10703903803000001003a240398030307080f1042c500140740010740e520140242d40c0600002c4e042c5010711a441000890414010001d401c4400414100345065891882d080100740980400e0030300f8004000342514061010300d4107647d00070080d040101002035904e01001c12281710501d61400c1ca003000819850350460150002c1c052002c0301b0200c524008044d0001d8505e0f07211121060a0320143c1c030181d070000c0300350382e201d6504a50100c2d0b9503c0b002411900d0380d0b206805042c415181ca11205840030304080358610760228241ca030240406148015000c441c85182e425415110ba8006805054414030303100c2c00b1088002c040c420b150f01d1301e0b2644a8059400c95402000d40d00003028051304580d4411441d5070403400b202c2c02d610300291111490f4480ca102c405081a020001c5480c1081100000789541341350742c0038000308452049410000c0102d042503072411410352038014007141c1548941441030584 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 838978920 1250 838977670 838977673
    0x290109090c08030f1c021e12160f0815041109130207020d0803090a0f0303140f01080c130e0d05070c0e06010804020904030e1203090411041a0a02070b0a0801090e030903 74
    0x190000003040311404500c80c005000b00c0d400c1100c00075641e698291041c07080b07001c00f000d0b030301c1389031000c5c1c081d050303003000f07440000c427007240807070786816160300501d100e011072102d241140b19130703c80304161041000720020441e8041d050521002265401c00040d00b0700301e600b166030000030311200c10900124441c841c00030b50050354410100001c1140320000756000000202103c0b14031a240d00c1c0c24002c5c403900082180000d031035425001c40600340104241d0081c50310320300046554500207015594001c1c040b60345004500c0d114001038644141d510882e031020300941070710240c4020074401061503220b907004441071100d0304d0002c42c074a9a0f81400c90b200e0b9070306840300421030b140ea03000c210408400420407001c010b11114442d07010744440280902d0380e140103000b1030b02c40280c0307420407042e16500e98010416503001d0104010204d00f1000c0f40702c66120200d515503031134a90000c100c1c1403105940280d20350501c002401c3e89850f134000d10050488801c1039042120f0303161503020303580324412200019450f = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 838980170 1250 838978920 838978927
    0xb15010c050a0b07021009080720010e040b180108060105121605040b0d050109060906050a091e0305040b190e010507031718100209040e06040c03290109090c08030f 72
    0x1010303000c1d125013061650045407140c008440c0000c00f606d0301d0003c1201d2003900802c2c0c40c000c01c186150881a40404426040980c00b41000001d10040c4c5a54089102d81d440e00c1180c80252200320304400d900001030489450396841c0ea207a00e590b80420b1003114010052201c074000882c030b003ca10049c110f9943c001f01c01c20240703413004010141c0b441c452071780d6010b10240001000103100344a1400b0951003850007080c40c3d50141041d030220b61000b0210000507003042c40010000d80183d00c40040710030300040089000001e0b08086406000b140c01c0715007034450000b5402c0300f000c035860714444800c0940d950f41045034414801151140281a8003c0100b500b210303801c0d080881525201c0e41c00000703001415185100100c200340fa202003030400b0861075a00280c0d48406040a0140ca500380d102e1800412090500e0ba655071440c4440784005030100b80401c918082d40440c83e46113900d42e00c020002c642c16540c5a00d521802450303058411a00e689890b0400100c940000c015a075038054000300c03460a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 838981420 1250 838980170 838980173
    0x130912050702180a061d04060c0509130207150204030c030c0506120a020702040f180303050604020711090a09050a12020120030115050c1608070e13030f0216030b15010c050a 76
    0x3d0701e40028010600079915214042003005d000b642294849800310040c407054100b500703018045450b800c014504003d02000583d0700d40d15600304105074100310320001641c613885030812909100d4122201c082d50b5000007400800c1c8107401e24001c058034003500312411490f64420402900344a05071812004441100009541c001da56000d01010780c0090b202060b801c609414500c1115080ca0a000c12440707040802800d26074144183c03640000161011882c1040070340703a1740b00307410030703444402c2c8a51841000181180c085411071440950700000712000f00149240180440302001d240100541c030f0000380038202e540c8401104100c07102403084e1461a400c220340c0c02e0300c0d050201c003000140b240810642c5030b1041c0400c09070210a1180c030310701072082d05020340541840100d6108909254900c414040304441a14242e1101903040c20101c00c1800780c035074242c0c100400c80381c0c01d0070f03d104440ca0000602c000034015522a01d0640802040354008500550b058190803602504541c4080e02d001c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 838982670 1250 838981420 838981459
    0x2103150e15040606091701061d13050a081804050f06090703090c0b030421170a060510080f100803040e1803041707231509130912050702 60
    0x1074100c0d018016604405420720003050075100c8552284000070b030150790810894500d40007030882280c6610082c00711524041c0e400c0d01101e9410818101e0403001c2000c1180e454140a484480e180d011094407280d084a090004d02030b04070003100381c129028004400070f00c1ca030601c03400b441205001003025668403803030305002040400034648814586e9400052001c21008910b030030003010900c8001c1d551f8500707480d103003d10144400385001c04141c41e5200d000f043e42c10001104900c204625100c85503503454084001900c420350001d900180c55845090030b0952001d4210311a1a03042030365119031716100f405401e422210320500741160000d20081c8441e21100b4000c9400188400d0380c841d514071a2010641581d0095005034010210014041050b03002407003160000c00251010f180c04206d1008a0300014500c0c5100328450402418846c03c1d150a440c140e03400e411380640702e05950072a05070280c00070700c0c04100076a500900c61441b4150188100c040740c0c04a40d014113100d100341c0c00c4030b9240 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 838983920 1250 838982670 838982699
    0xc060a09050f030705010e48180a110306010906350a0e0d0905120a1203140a0207020d02011206080a030915021b010c020a050d210315 59
    0x8803514050382c00058200759041010f440b030203006400008100c24220304c034904e001c01c3d41c010401500c441d02c030544403000494469410504003e201180b140240b204007007042d82d0756070f1519030300508001c041da4124140004861098014000070051101c41c02e4605030940022234116000401c1702000740310301031050803690080707100b0b5030021090405003540b40e842c0c08401003000e055136464030108141a4002c2c02400808075103400034111a1201c03800090003012140282c83c064140c0100700407030b1041c200240d07640c41c1d4000c51002030b0032081d45401005851805046942c21004c40049025032001c0d01c00c840701c1c154010400b0440c0c401a40c0152103c4a9401d0405041a650742d800141440d041c400e01a4007403107903682c500d4a905010b41c0e4002e214400300480210360285008004140340244d80135102c0c1002d003080740070890944002482101183c10498028100c6108002080041189040b04041d20360300f1200b0341581c900120101c13507481500380c607040b01e035107010020b611000402 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 838985170 1250 838983920 838983923
    0x2e0c0b13060f0c0c031403220f060e0609010c080108210c031612021506150c011506090b030f0103291005010e0d08030406020307210b0112020c060a09 66
    0x842c544810511102c11a01103681c1000825a90300c2e04e4000c142c0c2c010b00b03a004e02030840f0a22420340c2018070114038650501c015004400081c8407480e018031590700702c655009940804203200c24220840810b40704c4d6401d079110307034041d801e280c50fa0300018022000780e13041e140c20400404270303944034800254601d401c0301031a0030309180401001c8042c900a100030302c880c404008640c01030040c1480d007140507401640da031000315000022502a1700e55030311207964001300100c410385100c150306445c10400f81700d03d100c2106290301e4101302100102622054000b203a4083e100c024190380d582e201c40e140380c402216801021243c0e8401400003c03106015550712400711840c03444070103441015100580f1040d1044580c00b034044204012945e0b1018840ea420fa100342c40c0c82207180c0d6203598460b40b500016000821003500800002c1409120300f5124001d13030041264171151064900070400245108462180007401d95980700d0341c1c1130303c01d000b10380401ea414001401c05681d0441003800805250a0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 838986420 1250 838985170 838985183
    0x620072d1a0705120c1809090c0d0602041d090706020c030a03030c0201110f09030d1b0b0a150e01080d030605010f030e1e010b09090d020303010e07020a022e0c0b13 72
    0x84c07040c290700c0084060307100750000c20312103517075100348503820800311114260240314580c03000800c00c1545010410300707112602540c842c00c80b10420f14001d00070340150341118801100d500d0504442c0c90218031641d004107491030994481c5034440504980701e4220800880d01035000200c5480002d1007540f01020112480c4000110709849095000103030f8813a5034005d000d001d02040a400318602408030752400f18a60620503554405a00882440c10060001a1852603003078001a049495600102c0600e86109a0015101d4030703040060203912080c0a92080d07071281e41c10002c9003030302038824802070b00d005031101585100400d1088003e031031030b0040a1074500030710b00544608030240f40c04103e00d0a0107000070820b180140240311a19100400707800b040d500109440c0b80454010084034156901c03e40d42e55050398030004180c1c03404800000003900709400c13080c920130182d81c4422040361601e9224a40c00100f038180000c46074200c5010700502110b00300300c04182044603026604120078850355 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 838987670 1250 838986420 838986427
    0x804030c08040603060501120b09071103070819020f010b0619051903020a0e04090206040b1b102007050d031802060f0904111201030620072d1a0705 65
    0x5403800d007141c00c10b034407890110307032162002d005541e0881910754030f10030a200104420504900003c25481c405032040302405001e090380f110701c0340140202e8444523080404980d03900ea84c07000503001c042c5e443c0344220060064299510410b40107005141c0c04001c01401c50307081040c10280005004510002030003880420442d9125100c944100d904032440180c07030050304c80c503083c0806024404d031119070314455807070300d100c40c401681c558041d141036540c01d0b02982c3e00d0320903010345101c1441710741807807904070703c80e030310160704012103541241010420303400c2559452141c82c001c2e45540c1c014040024a250401080d04002030300c40d50040040f0010070032881403450058010806071b62110341c80a0941800040880784c0b03007498010302c1d8100c440d2551451518050015592010806000003001261501c50701050401c2c0c0b0305080528003c0004031a1340c903015440c007030044240828603070b4003140317200c0550104007034039070a02c2c002d0680002400304c010134004109208400020102c0c002d205050 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 838988920 1250 838987670 838987673
    0x140d06080607080a050703020c0a060b01050c1b0a1502100e07051504091406010c080c0a0605130606080f0318060d020415080a1802040b01200c01030506031c0804030c 73
    0x80200c180503510b1601c0712840760601e0348111054810092a10f4207140c0100883c1c00d1003480024000801c54204400050901100c00104c400b84038503804059a4810045801080c1c800403035508440442100d0048103203980f2030f0307070325060300070003640c4405a0040d840e40c00c1e0051082e0881e010f00401d100c2038031001030b1110009184c0103444600c0031fa461401207000e100c001b00c13921075030a00050948002e005441d040700000c08101181200404100b0003290300f110303400040003a00d40099101d45c05100360310700880480250107440c02d041c1c03031860504070002486500850303410307a072180900103146801c14070a07500f1017400d44a04444d400c91000c108504903000d45101510190607902500681c2000900000741040c030054050b07007146190800c0d00c080e20084040c51184690b050b10045200007100c00169040004010f030210a80b40203101404684804154450035203000d0301c04002540b42e44062654032030341c1140c3d21860b00d0000b02c403425170902030203000d68420310a107880032120304c00d13 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 838990170 1250 838988920 838988923
    0x31d030f0c0102060f04050d051312061b0c11060c030403080a02070519051f020313030c060215010b0306010e1c0c030b07110d050c010e16050103140106140d0608 71
    0xc0414000180d0401898000075603418000a078010041044460603030405031981a11407000341c4128050001c0001c400d076034200211503540003080710303480010400382141820300242440300c0365079038100800c014854070300f80144840c2d403c3c06c2d00030340e141ea2001280018042c0c0b40d803150076090381e980f100344800000164180014921524075901810b000f6107424103101074243c54551500b14030301d5802040c085622601c1c003410540d1098400c040c2c65000320f603410b034214070804e508004420182c03d00030040c8091018001d00b21040c3d40c0c00c58030b4600500d41c0e0000001428021600124000c001050080d0310582c0c4029440c5c400074180303030030030140c0c5000040070b031204030048030011a005820000d0021603900d503584030190b418040d40311000c13038003180c0d11860b00303066040c1408008552034890102c254005961005840212102c484e0003000c00011070790184204e5000905050f01c9207600c0f103642094504803035590b2140f090700a8121400007041d0000f940c144103d940c0c0301800241140c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 838991420 1250 838990170 838990183
    0x31805030a060e0105061e060a030e061618050d0609030e0a2315030f04150f06090b0604060518010302360a0501020a0b04050f070b0307090e040807031d03 68
    0xc90300c2c00003182442031003d1800d441000b4505442018500580000b0030b8645800e010001021a00990b54803030544054005000d900c450138407511560041114051881010020404681e1900010130402c00700d422071004050069941140c0305203031810009010790012040c45200e0300b40000300901d13520204040d505185c1c081d46110031600b001d0441e0454040c42050050300070346043ea00e844021410645130311001e01020b20b10902c0038005024841c900c03110b140e61440381c10050103890416252000500118003410040d5494030440c400140f820404076011100e240c1c84450520702c8441014070b00307210440806051640800c0181c1c01e0140201c0703c2d07000c0ca42990140840c02410001429801c1810150540620303107880c420310590381c0005e94100901d81c424cd040c82607a030303649001800d0400c00c040b0b0810398400c0142c0401c02e110750201442c800e800642e0b428000c59600e10202a03031204c04e540281018008000010220344520b0081602c00004000018444d901d8000300b4030740340 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 838992670 1250 838991420 838991423
    0x1e1509030d092109050d0b06010c0203030a2c09190b0a030b01080d03050f180c0a060f0216061407080918010f0b190302070c0e070504030311010216031805030a 70
    0x400e925607446504402403103452110b41880c10140c04c60038940492000c4510308006030171040d000340014110303841003641d50b464690107003d403070700e40340907030406016070350600100c2e480450750008003100c40da0b9054501155400040c80c1c0d50785c544401e65000005942c08103030798509600c0f815500460784652440c1802184103464800742580340010241c1085040c5016508060504052040c078403401c41295800c1034000070111003400e140d004040c54889410130399034000e8445000003a2203038104007082506550754090718841d8041c43c0340c080c505203841c0501c001140e42d035060050074001e0715002d03150451103503000510b014441e20016800400c100c03034030744001c0e02050051100c0c61a4074030f0f404c0180b01c05188a405d2020760245100a5403444909104140d030100e11785007444080ca00f03082c0106482000c0340c02c80d04045c580204a070340580015004955500329107003c400c2c0500c00c84d006140d03070002c0303010942d00a40d8102d03440740060b030884003000044800441d10340e0b03050125643c0d56 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 838993920 1250 838992670 838992683
    0x110406061e0c150c0c0c0b211b220308040e01150512100509090601090c0c0302070b130e13050105061e0f03070b04090e07150c0609020d0816051e1509030d09 69
    0x348e03440c000100404080819038280b0000c0d40003800122046504a41c203009180c09810f13071102d108040254903107415a090300070310481d8200000610607088000c1050380c201401242503a0b032100d0100b071440c0c130741460490015204004070046010301ca030382203800141d0420000e0a456075800000c0d1f01c90400e40c1c404040390400c500401c140d11280c483e52000c030a8500b4014040c82c0680c8010313446d00050f10071002d04120001e054410b10401406d28000303040c014801c401141400c0511680e14641e40d60121417540c078000c0850100c0c80e00e10a030741c2402100700008003200071407100340840c64541c0d10120f50580b0816102180e9000364130054070251105107070001d95401a41d5680c1e01d0012113a1013401c01c001d03007051044580f6071003c06021003d8003c0000f09a07000f00d0710200750303a491a0000580b284201241e05008a02c8c00300003144514050008c54050340781e851581d0007128081c9100c0303040d0340e00051020710369202d12030419a000e01070307900340c03404c140c0003c1c114825141e513a04102c0e602d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 838995170 1250 838993920 838993927
    0x60b090906160906171302060c0d080c13180e1009150509030a081b0d050601030e010506010e1005130f1e0b04060c110406061e0c150c0c0c0b 62
    0x501900903a4100600007a1038101c00c028034014005c0c244410903129810507098250025040e6083d082c0808026030b4081c00407966a00407000f01038940c066161014005406100880c0e04003001c003054a00244c0124410140760f860604080c0a0041c00d00b200e141c49519910013080a61061040518409626801107034003032040c5042c0011080441a00d600d20740740c1001d100740040e00105032040c4001e04c0c02c1085851300e402400340c410080341108210f20410009005008110301c2c0c1000e4040c21003030720144081108494018241c4108441311030000b40580388100c081d01c0c000c100078040ca00142080382c601580002d01d05141c2c0ca035a001880b5004904030104100c1081030340c0300c01c016840e614030020950600000c2004c84c03140384641c03400c100880c00784506100c0c1c566031030b0408000050080048ce84e442001400038000c09503250481007080c3c0204c030300740340504a82040c040d80030a2102c805c528410380380300203058202601d01002603074070b02000000c6103027450b40094100460210348 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 838996420 1250 838995170 838995181
    0x190606140402030f06041d01050403030b0a150206160c020603010b09030f0d090308090109150f1101090206090415051804060f0903020a2d0f02041109060f07060b090906 74
    0xc501a0306a00e6801544100300300007201025094075908004120340110b01022814103140201801d6203020140d5443e0074140010141c240d0310540b0b030f102d03059406a80e03403650307241c01000001010503220056080403001903101c681441d4851200714250410100a080c50740100c0d182d03400c00d80100e50f4041c2c00040481d00c914040080c40d140d000c01030001c120034240414010203004940c1300c020170b40500422440703090fa00030040706010382900042d8407802d0350403860003065040d4070b0548001150601c1005640700c41d0601646031503c0e00500f541c5c0ca030568071014480100007030040b10314080c40509000c11242e03200d0382ea42241c3c40200003190b41e03e040c0750400a04480501400c400038510300042400001e0f0003103960504e480d084004206443c1940420207100420303071145030303c160750900700e500400129504c107400c014000e850800c5140d104107000590340c420310300c81c81d610074820b102980b01881410300806120740700c0c41000c1002c2c100c00300856840207040c2e0300c0000130b0704160304000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 838997670 1250 838996420 838996439
    0x10e0705060702030a061a060703021e030301060e0607050f01091a130b130218070918020301060c02190b031e0615030a0b011b0c031b080717190606 65
    0x10140000715501d5142011690002e84d656041120041c045070711b80d207030480c840c40c2034a000c81d46204c1c068045607071040d841c40c00a4032070824000a0010f1f00549100c085a5000002a20706a400350380314105105040030800000703820200ac11a410701c203980200001c60790a024406206101e56000d03400c00c042c1e2114400c00368001056508095800162540400c1c400d0740043e0b00030b0340349155038180c08294004a400210928100f170501519401441403140d03001500b0802c80d000039135129001d281c107401d076500f40d00c800e105042c00184091201c0c00946070400d001c0801301c008000000f14195a0383e400440c030380088900c4614070480d88500900c0034100e0411365806802191009005402001451028040580007801050340c0e048010300c283d0080c554120346000300c23400c1d48446806442e012480403114001258070303010700b50034044140c4a40c4861016990010082c281a41c2410120440c5c8010703403a12034081d02c80c0d5400444009544901031032014003c6c10082251401c10f0070a1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 838998920 1250 838997670 838997683
    0x40e191208160206010b0918010810150302090609190c0513090e1f0603020a08030d1d0d0c0303110a0306080c0f090606090f1306090c082401030f0608010e 68
    0x90103203808446004820701e0f80414030506450a60048503102c2440c4804901019643c00c800c0814143c1c4100108445030300080d00c1c0f00c0840c0741d01003408400b40c8001c42240e030b081107110007500000c07040040f51203450101c124581c4951403001c911110002d00307000030305480c881554000030401c005103505650301040d8210000c2c1412540a1090a03001042d0564030402100c08400d50240c0d040c0d8500c001c1c1e8140c01c620000c540041040c40c030182c8031142542c403036014605031f4049501d0480d047e0112000d40c5d0942008084400280a0704051b03c0000c4d92504a42d8004404165407202c0c00c0040d80740d00b4014140d5045190750029186091072081442c24880d0316245100d011251b8802c0da00d9915229450390080d41038039116126801407000c070f0702ca1000491115400940600341c000c07004070aa105d0004c841d2820814850780da40c0c1001558030000507503083c20400d0700003880e10b40d05030700c4003420a10200185800904564070401c0b503801c07603c0d103030401c0364542d4442c128084980303001c002c3c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 839000170 1250 838998920 838998931
    0x901020307051b3f07120c0915060c1b0e042402030907061b0506010308070c0b0a050f0328020d0b0301020f1605010b1f02010c0309020f040e191208 65
    0x2404c08244d0381c0603c210404003400000d40000000540c0301c90742403820f0100c113004100ca89840c60241c546894940500e030740c0d50043e00c00541c0b52041d01000d80419481340b00403200d540c0c50b090b004e10210b4603104a204100c02c00341c3d00c080d0400c0c40024469185c3c0e00c0440c03066004510b241c2d03e102d0f85030f51460341c0c00302d00074142101c0b50040c01401116003021850004803a080e003040c1012110700c449400b11800140b1025146024050000040c031142d20010b0a0862141441c10080f98a907480240940507030780002001800501085000345094001540c103d920524000003010040025250a050f5040b881004076008030b80170261035414040e40e016410224002d606205860076a40d0483c020310600c40c84000e01c01510f4020300900b03612550801c4800350040000c400078409002d041c0304075101340401586044440d200c0319100384150316541c0d5004001e840c9a40b2401c0412001d4040c40d10740d1802401080240b005600c500300310160440d12500c400b02c0c0711610f503a0003502103e0000d08 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 839001420 1250 839000170 839000209
    0x1501020d0914060d1d010912022a061605030903071a19120207080403031403150609120a0c030512120a0510092906130504020901020307051b 62
    0x10034880c0c5031608040c0600480142c40582c4c89408414100e805404103450710760102d41e0702c10318000300b0403040d04400900e40c06071401c1e0004054012040b42e4600b40705410b00c1a24401d07558426241e0350849036507140d8400100024140507071a4800d030030503041d1180460303044e0710010b10810740e8142441200c000340204500003e481d400124207104c14401d01100d644080b10441401920070b01661906810700d8132081c0464640c0e0742440d1210150344a80810f80220b144001c0381400e820510088903c039000b0040481601d05203c4107000c00f51b04441140c0f980113010750001d84108004200302260180200c280524040c44e5007045800e041c0c8031484c0914100c001c120411750b400240035515040150341000081c0c980e030b03044202d006400d280d0803e4689a082a60031288950706001e03540540919055080d1003150450400c491849641100218655100300810061806d50701500000c01c060040c2c83c0381c41030b540d81e56410041080140320030b51448124103003440c00d1284100700b0360034140c007 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 839002670 1250 839001420 839001437
    0x2030c100216050f0d0831030c0f08040302042712030204150917060c030f0901060521160513020d020706020f0d0c0f0c0b040c030b070e09060d2105040e1501020d 71
    0x2032141306c0c1011f1144980f001030404108100c201482000c3c016403898103c42a0307680c4041c107141942c00f6900c60302c016441503042c41e00d2002800c801d08030206c2c590006455400701401c2a964060411881025103000d0590900000400680c0040ca121040307100740d0f10f078603078141011500e438000000380000c0700007980010200407440b003140d8200c07074009101410581b031030340c0d4541d1400e001d0301050708031503048040724040d210004000d4000d4203003140d0410079125005003220200b606680c04c1e2082c00d17032000c40845542c860740390303da00510706460380c10f030301615190301c2e03450355801c0c1c0e40803200342d18625070001144c0160040c60700c078403104681e00f0300c0d20380104492204002d0004241c82e401802c010f15540120b8100290120071100440d4030240701c66203403808620180080c4042c0900c00c0c056170040c0009441c0d45070070700c1c1c48a42d10342e01a1412691710300c0c11400d05104401075001b4020b00038100310102d801c2100c82c00d21131041a1a000c01601c1900d01d43c00281400340c9501020140721030701 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 839003920 1250 839002670 839002711
    0x210a020f150408131a2703031c02041203021f0603030903021201290102010e030906031f0801090602030a0f02120f0606090a140a050102030c100216050f0d08 69
    0x40d0305450308590450390550720b074419000c480e00e1411241d4844042d541009002c0030407141810080c064961b2400ca243e542d1002c24458a00c40010b80c0c03040c40c0d0715410806c0b00c1c070b8004482c2846d422002c01c804000605003500c89450441b00c41c4024000d80244c0c1c00300105117502104c8e59494400d4029507402808400d1039076801030312460503408002e20440f40c04207802da41c2e81096000580002c10030514100340f480c44000141d14039a0144442c3c015428100d881f0240007000044600e000b00140106d455540c0c3d0403818000100480344410001c2050140014240402d008901a2600400e0016500e00304030100300c00700c03100800340c1c0c5492801030043e0400c0d00c201580341940310448034100d060654900d00040c40a124255190790300000a580200708004819003181a4200035150711162030b07103403401644c1e2806445d20082446d440051580c4100880ba000341c080300212078580a21000b1540c3d4060500d040e494030141c40d03500c060010b0318400d9201c910103403c038103031a80305642c0748102c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 839005170 1250 839003920 839003953
    0xd020d0806040b0d0503120a06051005161406180105010e0601020a11190f080c09060d1106040b0a0509190f090b0a090501030c15030c0f0809210a020f 66
    0x2802248110350390f508848603030303d40d013a4004480383d011040d6642d03121701d01000101c0444c04d43d0946150751424402080c1800c0590a44640251580f0351500700031414050001116441c4000c4600556181900b04200800c0027041e0284c460f440701211009003650410f402c6030416400300042d61320420030701070140d80109641d09840c1c1c1000001100410020116100050101c542d2400b64903081700040c5012041a20b403056070303028410b4404080c6400200700300e501c5c040c0c1e000344c1e0040090301c41d040041c2c100c1c0e074440c01100e0040d241500b0140d075041e02ca40b95800640441c404200d00140d90810b503c1e02c5401d00c1c103000140c046044201d4241403411920404500487d10381581e5850003a42d10340e22402540000c2c4542c910621581d83c403480c102c04442c02520960a80044209003041054080c1c00707a40e050080c82d80d95106010044401202c500300094001145030264089494400009004c4107000348481c0400e03da0790304900000900d84818048160b0b401c1d0045d544030404c4080 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 839006420 1250 839005170 839005187
    0x6150f05130605100906080c03011410030f0f0606110703170c0102040b0a0f091706070c06090605090f070504050108120c19030903021819020c03091c050d020d 70
    0x50a0740e80d2580c00803441c9640c0c0040c400c1d03810895001c0c01d030881e80003a45901030f1110068540907540c003642600c0e11186007015000070301903030300d1500d00703c0710385e41c9241040550380703084034154540450700d0300602d0416003c550216003081d1042e5101c0009000c1181c00c0460b0f01401d4080303030028404076145031958403120140e550b480303840481c00030300060f2141003501510054164204426500c5400c1d180c00380541d5000e0300410301240c02800000792804013900c40c4661184101c0140c51070b036031440412034100394034030000c4654075940c016000c0803608c14400c071071250a1610040264045840901e441d061041c1d000520035400c10005120200d000b103205011007500e014201c0d00c628003071000750b0400840d01c007201804085000c0d810300f495402448141122300a441007010a001081c05549100741143d40d03103070510240d000e07440401040d900420741d032480d030800d40e400c014042c00000c0d80c07a070310042442c04c1e0301c44124501080c000c0034410700d001c403005400100f4103c6051030000d0a01034 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 839007670 1250 839006420 839006429
    0x60303180613030b0c0406082206050a020d020d090309050f061204081603020606040b1f0c03090504020a03021b07050306011215021902010c02030f1204060e07030b0406150f 76
    0x310080b84402d80c01d980389809101555102000100720b10340741407118001d400501c00e02001401d1394020400700006116000f281c14a5000c48030131030401a207409019200150442201c96420081c41960040c54406402c20048601011807c411a07040040161302c56800441c860842801c0d83d03000c680c0d4401c21601d50300c112006441c503c0d81c0e02d00b0300e100940645002c01141da08059680401c043d400f240300c5102e120300300d50801541c1e042c00c00303106110030000b100015030300031114221039031806001c540000301d10a1034141085611580494240d802060424010940100b60407d440704580100c00b180603d96000303200180c50a000240c0d103d9042c816502d014440301c00c40740a10106010410021200c254299540e64503070790341c51826801d44e080380780107510309035203541a41d00c08011a05034030a40e034069420301c415048a2010410064801c41f481c9a544034018024013007400305400541c002c0c1c0e5004000c0c40c05007406401d40f0007040294891211004003405144292410b020a0340d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 839008920 1250 839007670 839007679
    0x1e03070c110f030f07060206010b1908090a171e090a180e0d090e06030609060a0b0607051c080a0b0109060f020a020d0506071205091e1501030309050906030318 70
    0x1035000041008002c0b00e812a075058010180410f0684600003000b0f0101c80460b401c607074950b83d13079665980d1075001e00c54100328203041c2018032034181880f426440b5003000000003512030600b2290350307018446c02d100308428a0b0000104400340110b034a00c0440342040180d0400700d00e40311040001540302800f6008441c6070540344034061480c0400c60b44a48001c1d89047d04441410300481c00241c010007983c0b00b60032462503101c0000d9803d0401041d014000c0701c2d40c20080c0f1140d15403244820281a0002c2d01c0344e0020024442c0c5804031b801081000e4030407112004080c04d4100d64072008001844c01001000078030b04220302c021060760b0119022007202c0700c6181054240c112118100c0c01c140680ca0f01a502940700500b420511201198090060f03026885400b5102e503194040003e03910211001c2c02e0b00d411142d250a140340400d101ca81c00b105400040d42c22100b10b41e0a00e1540007400c1e00140e000940d07400d002c0c01702d1b003006d944564000c00d0031002181808211801450440b52100d1098000c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 839010170 1250 839008920 839008943
    0x5011e0504020d17071a01050a15020c1002120f0d06050618100318051b032e140a1a12030904110d020f071a040b01030308040503120c1e03070c 63
    0x800d13443d006503552150b10800050380c9100d00f45442c07250241c280038072031043c0c0000d20002412000d06040411200c0c082d0041c1c0307410000201080030312000341801c00158029264131381004903261004140d10041040b41c0c540b220b8403080740c0000c0305e42036040180140e5080104145072a10024803000c00241142e00c08103d0314105011000703072842c110f150760120100707640072041100105020f00c0c40c0710000100c420704882101050398482d00009400f00c20f2030910924412503004040a60090b400e9400200704205020502d0542c0101124039800c89031350b81c000e02c001c0643c1d000507003e411300100e0301c0000079200c0c1c030340d61601d922070424000d10865503065100c2060044400365070155081250031922010081c00b540300560284c40216150004c0702c122003d0000c00100c0203000b40e030031038002c100b02e82c03c541d016104840050015200b610080c0711a07010001e0b03640701d880c42968690355250701c401c004102c0c04c01407800c080c1c2101007070009204011140d5400b401401145070030500702d080c1d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 839011420 1250 839010170 839010203
    0x5030d1404034118041b050309031201030f0b100f06030b0a0b0a020313090603080717070b0c0d0f050c09040f0b030607091805010501050a0f110a05011e0504020d 71
    0xc03002c9003526250004018109581c1d081c000501040c0003c9001c0d014050b50807001c0000b242c4200351240d0383c00346c1c3e170340540c8207042c0b10f40d0141d030380a071500301240d00c0c001c008440240310040c00d074402c899002e000d25540f0b080000d6082d40640015041140c3d80f070540c140036002d0401d4440303008950405940d00c0213810180d6460800f080201101c00703515581e0180c10800079143c0d402600201008086240d000170810410b124410482e508220714a041c03070110f0b0382e241c00488943c003121120100a01501020429510040703020b0160000c007075030b5410b4544110010b440b80e032024140d5191410301049403031900342c0100d032200030080307500180d15040400c1240007020106240c2c6c1c0c05200e941d040142d915040b902c02001d960151180c0074810040041c000191b6409000c0d560000d0002d0013075100c0140100319040304e107000d070309003101c240205000d030b0b51401d1490101900c6ea0703034452804a400e00c030b000c440c1e040404c905010030b01c040c0c41c082e00881c10001c01008000c0544005980621 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 839012670 1250 839011420 839011487
    0x61308070b0103080901030b0a0b030103061d030a031b0315050108060d0c0b03011403240408040506030a0504060e0c01020a080711030a0305070c05100e0d03030b040905030d140403 79
    0x55100e5071020100c00e180d42c403410462001d40205018502103858070014004500e052101c0c00300f2611100ca60b1480d41e82182c2c1d40794081c01108460031003c0c019500039607800403062015020305109641e0000f55240d15461041c514411155502c0c00d0500e806014500e024140340c1760b5080e01c03421308002d40075445010110b030b5220b22019020b06507084582c800708010f03144800441c1202d4499003011002d003d10b408041d205d000391204041500255100350751401d010500f031543c054000c44001e030905964102103612607204440321114241c0c1d4804210403c00c035407090050022400000f00f98145030b190020b550b0324020900030f001f010000c00c018081021107030403003904034800707019079030190307094600604140c00c455001c0320250b40006d40401c01c2d00f08803002128421541d1740700c0300b45407160411300841c500006410740426444640b6905075403618060042e0f03092092005641ea003107a0441c1c00220380c0c0954840340059134080030300002ca41e02c00d010354000c1d0708a5018500100f00c00c40c1c0303035 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 839013920 1250 839012670 839012677
    0xe1902130212041401140f07090b0a031d010e0705090a060503151b03060607200402031f050a05010519020a0c0905041407061209030c080f09030709090203061308 71
    0x103151800021442c50420b02181000e00442c89081c00b6031892403400f0109080c2c0d2010180d508000744101c0000f40c0150321007100940200c41030a1007410192607815007007096000d001c42c3c8010940f244c11b00c00450718a1034410321a408128001c0002084c540c00e803941342c016034820f581c42101c0080100303c400c0401c0e40820014500142280d5410307030310211403140f00d42d0880f0145d03569001d1000c2c4000810710401103d100d017100800003441c112155480c075074031a03940100359030540f03d201c031120992b841d1071004502a117091004050302e0410f0504400002d01c1c07941040e40921a0745e1010402070760001c0582d2404101c0351620300f401c041d8103104034076081c60100040c110300795a28000a24400f42c0d071000380218010201c010042d4800340750309990f50f105200307120001d03110192900700e4000303030f9203c042c2c00d0748285090b4a5014850710f48000940051142240e550350000b0300c901d041c50200031850046c801031070705001614507900041d88502000341020407240c0030405880810402c842103 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 839015170 1250 839013920 839013949
    0x111e03010c0806030d050a0f050c1015080d020106080a02013c110a0b07140c010f020a090f0612020a050c060f160c0c03060c02070b120702100e1902 65
    0x304a0300d442444020000b80c1c054a5150107405005003492007103229104582d4860682d031191280081c20a82c00c031442c2d8000e184e10034040c01202c442c00c91092542c05150000d5102d40300070a50a030074044001d0420700b001d020b44095a151220800000501003601e11340c0a409007011516a408107100c2c04c1c1510079020760100210004e079400b036204200c100402c42c104640c2d80d60036822581e910216580700798418024112810304070000380c05500c03840c4800d5405204900c400d0074001c000980c3c0c3d082d03070300c1001c50620b6184c021a2070112264000c0803980103107441850301000074900b1001030202500d51029140880e00020310b144207501400c12240025504422500c00745485240c0042208007501ca807220b111540075600c2c100c40c4204845484e040c0c10500c030240103840d660710040100301849007401903000b8400005507030140350001e04080712010000740d440d803505c6a002800d016200b00c04001d003c3c5010355800c8400b00c0016a8030002030760003420b83c15031003180001041c02000505 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 839016420 1250 839015170 839015173
    0xf090111070309230d110a120804090c080c0a03020f09090403030504260a0507020a0f0b030708072a0c0b03092103060904030f051c0b030c0409111e03 66
    0x3500002c040e48040b41070111100490240f0205a45102160b00201c10160166028039a8088180462064035034008800d500402d8003c00b41d913190300c0f0310100702e40d007a07050750f02c8800030030f041210150b1400740c450240280e10b8154610b1070000080501d42c010300140381d0416901241c407410a4100c44100c1c0c048a1000b401c2000d0741c5814640103000d13042c102c83c00c460701403075a58082d040c0ca4502101181440385540c03518104001c901048940360007289090380e2000c03440500041080c01c0441441c06403402070001c070f6403440c0c80c0e50081c0240300c000e8448010810604c800303000d0f6550340c00b1002c0c002c491054041d90356804605040361030f140310f0b40001d402c1000001c18080031480000e6600d900d4050102c42001c00240c0140003540350204540a0f50070110140005d000a4851481c11580320101d0a1030760a188001c052180c0700050b00c8220240c0f9030b6100c040500d540780404c8981c0407240308680501c01e10b81669105603485a0194140740078012012440004800c1c0b1803080c000d5040140 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 839017670 1250 839016420 839016427
    0xa090b0c16202d01051e04030b040302060f13020402030a0b0a290301180c02120c070911360d05070509061f050d0f0237080f090111 58
    0x641c08030024050071001c501c295825a4030752a56502500d642407500001c60f2800f40094414006450691040c040003861060182d1011840d45100b0042d0002e103000301d0403d1b501c2d20301450040d1400001510849880c0da03007000b005598000c03081c040c101240c0c150783c05612a1512200c3d10050480c4080c0980e012100300408078661403182181e0f0b9081095004484d1920241600c80016200030f0040c41311411626a038440d50391750713a4100c1c0040e0710040c4100c40100042510446c015003210306118240c4d040f5203000c21100980340605007107880d190020615013000101741d000c0e1030580380d1000742c5c000403e801c1a44c40038203401c91802288805401c0c100820500e2404a40392582809080e1045070450081403c90419201300841c2100c43c010580003080c024106071070305e030040c02d5158015a00c03502c911420150a0000e030405404c04002600c518030f000c0c0401d086d50b0b1115415a54850068544151083d8000042500030451a508a095031203a402c0b50780508061019403c0448000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 839018920 1250 839017670 839017703
    0xf0e0301180516060e06070c0803040605040306111204030305092401031407060906050c0c120c010806030c030a060b2403341803020a08010e060a090b0c16 68
    0x295410782120344548240d58210090845039007a2107454010540003c06202e00d2500c242403034001040007602031244258410783d140d4403540b460f48244c11200c002800841c04008101c070740d000d49180f15201400e8103003015401020006105001880901010b4035800880c1f21090180070401044140900c0d0369040c1c200504025421b0360b0a1008843c1600401c1c007500390f1070408138502c0151800f994440b20310501d4444101c1d0b442d00200351010b0700c0d000ea040255015520851140038100e00c84010b0300c528240799001500480009003190301a0300040011005a074021686050095102c0c1d400581e0002031008506100030014810b2302006540418403941035a010240d88220814a02c007520403c400e82c60401c0c0d0170100030715080c0703000c03062514012240141c40c0d20042c581c1300d0400900380d60380c1c0e0300001c2034500140d20520641c0d54a102c090202c1d081440056407110003600d003030050b4901c5136200740c0d004100034428001c1d021301041c2c0e00b80302c5240704006071070541c00016281020303940 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 839020170 1250 839018920 839018951
    0x4060b0318150108030403140c1c02011b0b01170c040e07171923100b130203460506010824090709050d150b0a0e070f0e0301 55
    0x2481016a41e0380314801203a01a1500700b0390b0b160507a62914090f5041ca4a5661198041900124085040e000d140d80d05080e80e1101012452405031100c00501c140903180009002e413000d0001032032101c0c04195a48001c0360400090904540f84142c1601251078840c81481c24000706c09060355001e801d2121860f03050000081e9001520941a58440b290a001d406166201020480b0340141c10740d5010035808100c0c188090030710720001201c02000c0b0780d000c02e950b0f07041404070400300030843c1c1d58a65040302400d1900706404a61264038045265040c035010056058405450800c3c400d0302824501040a074240b000d034820208201c0160503c2001c0b01e4040043c06003100c0040c0011741820015140c0350340c25400d0710106000b00c2078445958000000d0002c500001881e5505000702d80c0c50004140d2190340114801e00d00444c6200c0340251000810019500344868a81c426000c019052003007128525007036400845c0c50915071240d10f65007a0176502482d84000c116855407a100414081050 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 839021420 1250 839020170 839020201
    0xe19090207060b04050c03070f0c0309030b070f030c0507051e0a02091302030c09152e0201020c011a10030c12020c0c0102120301060c0b180708071403010207030c06090204060b03 78
    0x4444c24811a5642840e40d89280000c03600d940000300b0510440c14403d008101850203940240703010049661a9150f03410244007d03a89440000c03a42101c0128040e810310540c220706e0380d1450418502421902c0b0243d55078500d0003400c001c0000c611040c8002d0004010800150f503000c1c25a604030300e0801d0040050381c401c4102607000340180c81004000c0d00c2c04100441c4501031014030b02c030000184400f40125444114610705502c101c90a03440c504502c03100e01e450544840e0b07800560740c2c80341b81c10340300d0079190100000094480c0040107441035590b104c03801006c403102e40c9400500d640192500302c03064410303280d046220074400120455204001300d0804070454007a0200c130305248406802c14440d00c024450340380012500490b0300005000b02d0101e81d00310440c1d0041030341000c1000d800074104046640a0400c5030320460b0308000c6407400400305411084110300071030410ba201e0b1409014801c07c486c00910150395100c8003070841d5601d903c064003a12110608940341c2c50440310b180f08009 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 839022670 1250 839021420 839021441
    0x70302120a090e07030e190309050307030c17072303150f01050d02030f06070903050f151308070f12090803070f12110111040f06020d0e1909020706 65
    0x503000d03211884444034040310402403655880403641d62410180003551480a0225420036845040a0410346410003103800407039000d41c0240c402074054a00902032031804d5111700c0c000e800400040021030482d599407070444402c0e800001c02c4180500086041c48542c0e00b0091002030750104800d0942c000c2d20039140980b070242d044504084400001c0b0260210444003580141400c0380144018201004161080303031010382124960a01e85480d20b041040803140900001c1241385c0800900c4030402210a0f51980c59020701140b49a940d00000c3c040001000c040c942030b09070324268100b10303c1e041100c11090f002001400e0754210342ca891003040008681030f0000400c505808100c00f030000c004c444005a0100c1424052882661042c1102c12469010700610080d50312135480d2050030f008001a10f681c0c00d40d0030703960700d0a110075490014046e070071040866025445441c00940c0058014070100c20881e4000640303400001c0d4a16030010036088505000d001080000401c13400707801c403c8088 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 839023920 1250 839022670 839022673
    0x2120f03070b0109050402100e010203120a0207030201060e04120c0f02090a0c0909060e0f07030b03030403050a0339020604260d0e06030c220e07021b060d0e01021608070302 76
    0x20790344da018582c00e644065402075400380625001006560088580d545240b1040c01541c1c1409904008082d060800b101d40341c81007034000030440c041550a200c1c9001601d503440b02c0c100b490806440e201c0c502400b81c100c1c02c040c0507046c4220014000c032003803141000707a801800b80206142110f20034002d003101c9520b84000c2452084040380e121000c1c000d000036900c10358140707960fa6544640c4034034070150180c04c0300705045e6103e0064885403001d0005002450164005001c20345083c500280400c1d038000214240903074003c0c0101c0d250001c20f1219500c4144903000c0d40b1300d0101400002c0251040d03a20011b440d00b00307002c0314800c240c1d0801c2100e04003c6a00107035151107141c50402d980210807283c400345c0c4880d00f000042c44000d02d102c054040e096001801c0c1c00d140308901050a03204609800c9a140d80441340c007008032503503040214602c00d102c4a08135151a40c61034000c1402c50041070403c1302c40b15215800000e10450940c1615050440e481c5801a40402401c0c04e4000e41d0141c02c069005 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 839025170 1250 839023920 839023943
    0x21501080601181d011514060301050a0e3c01090c080601120f0908182e0e040c0509120607080703021b07180c140703030902120f0307 59
    0xd02102140840c122401e8403c100400603103503001c00d0007483c0c0b29480300240c4030400702c01400d4100c01d224540607541c503401ca1282c018144180c50301d0200540c44a107203d540e0070030050019844030340d410401c440100315030410300d840d0310245414a00c42c4006481e40c10b44000b100c4450f01c0760108403103090381002d000d190032507600c61050205030707403000389494041405074000c02c0d00d0354800c2c1541e1030440102c10000038408041c20b104000d0300e1002070262168000805c7c1b1001400480d248181200c50460f40f9001c4120140f00d9a008030881586c90050444410544c1980341c2c040c040764040390000400410810201b07075009403540d0484600c05028092410845800f041f00044041c001c00060b01c41003410340d12250110065800085800b10f107031541c5518a81381501000b6070b9001c1d0500c200c3e2600078410700c5082c841115594410401001610008801c0b06110744085030001078045c900424001500d0000c51810780381c0e800443c1003407040c6251040032801c080054a0300921078860606c4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 839026420 1250 839025170 839025179
    0x9032616020a0218220b01060e010203130e0a0207082131030309080a0306090c18050d11090901140a0b18270f06060105041a0901050d0507021501 64
    0xc1e11005120000d400c116425199610b00e08241c1c2940d5120f4400c3e540e1704000c41040d110701c2ca400c801880110b07050800c0340014401c00e40c000c654a4106242840158100040c0302c1c001e1104a00500c100720807050b0b030301e02040c080c003031a4045400c0c0c0c5801445141d542c8102e036070480054054440390241185c85640030508881d10180540125995080585466024a000c41c201005c01010403130502d940c0d000014006100344c40500884507058400080c40d034601050740381034801a4032400c1c2003003146805968124903080280059030401e96000301950468502a914016048007a6030710600c004100100810150014000c0c9200f0041a41580d03c030030703540005695079811407681c050841840748414041140401d40e12405c8146c0c08442502258240610846116000d2400c1e410404070f5805004082000c1d54100100b8030f402d9240c43d152554803456003035082c01e8400b0041e0005003008150f84100705480388a000c1013400c02c40b9041583d03001e0b42d203003030900e8250403000c052000042d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 839027670 1250 839026420 839026423
    0x908011404080715140f0414030408120705100e030d0e0a0809040f0b10021e0c0d021003020403061814010e06150a030f06150801020705030a030903261602 68
    0x70702881c0e00002d1242000e81540c1d4004032510f048800030a500e50352505190184c00c0318540a006061402544660741002c3c04c00301010500c003283c070400c0e03074000c0104122a5100040500000d48520036075511801c007480d0242c10418042441c80b2410f0400400078280704c00480204040001e1020410981d1501c00c01c0c581c5400049501130314006081c07207001c0a41c103044d04012100803c019000a80d60007000000f4141d8618040400061b88032810315036500011400d00100505500010300c4001001030016110240800001f40211029404a030b0001c5c042d03019034014592062050102110300884c05800070030242c2c041d03501203c560060880d51300c040c032820500403011000b4100554070010020700d07880850a0590708a204030400101041c088002d02203007070301c103603004501d982c0c9a40001c1c041b00041d0304070f22130300d92042148600003000013084400c400b00502f00450550224102070b286101c40260002c0580702c4411a4403c030300e0003070f842c64170407580c2d1945510f0350403a00170304030b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 839028776 1106 839027670 839027711
    0x1c11030106021006151110022701031517070f2606070e0907090503060411030601080102090d060203040206040810051506030606033103090801 63
    0x14410310360b06024003410035000d0301d41801845d0a040d00c44640300d17a40302c000e4003881000206c030981a48103000d0b91514080c166001c5482d00c4020000326a4052407002158030807a0740c00c01c041c044c2d0301901c140d40d00c01e5640c00280d20701d41d09242c80800842038060f101000c03485440c100140c0323021301180c82d00c06456416480d03000080b441c44803c20190004190000c590090420000307038a601003482401c6102c2141c0440854071080710944854200340c00c5244c05000300010082032200c0000c2c00b403c8101c0a0703085031520303a0384003004d078200d01400310f5860344000c1c018105000300b907450b00610703003050005003010303d02079445a42500c0e080443c12040d004503115000c000618504446808070341000b03840451451030000c0000d006484020a40301e1086402c81041d8007454030f001c3c0350021174500005c1590021050b0401418141413440b9030006982050742c25040d10042e074407030 = true := by decide +kernel

theorem cover : BRFrame.Cov 838848920 839028776 := by
  have h0 := BRFrame.cov_init 838848920
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838848920 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 838848920 ≤ n) (h2 : n < 839028776) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
