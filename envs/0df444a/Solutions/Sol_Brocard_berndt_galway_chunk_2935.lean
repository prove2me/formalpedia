-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2935
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:11:04.333059+00:00
-- url     : https://prove2.me/submissions/c67e4638-08ff-4b52-a6e4-34e70326061f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 527697841 ≤ n < 527877697 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 527699091 1250 527697841 527697847
    0x50306040203060f0a0209040612051b24090301110712080702060f0a02070c03150c030b06040b0a05390a051b0a030209150f03190b0403031d0a0209010902 68
    0x50b1030008400d034000346510b50221850780c940c0c5040d800392260b03202c0e107038015081c40c10000312854030315002c51915200c0c03030a68480559850505440386101c2c100d155000c01c100f01c81c00030741d140c0d0b0301e00128010b982500d40383c680203100011a0940303954807000d10040200060810902484855240c08003206d40f4044030303a4144504001e59908000c2c12001501220750702141007491198100c0d10115885100549100d5403030408101c01400b01441c10001780c00d010121880b680b0a1050092001005209a00380360500304d000007542c021020341c10130b1010800c021070500690305514100c810308510025010003c1d605120f41c8910300b00d1940d10700d503120074082400620003141002000c0340601040220704c04031030003d0300e46482c039400607401803240c4007804021101380031408001030341503640481074103545082c0742c7d030394641c001171040c2080340c10002d00009122542c1c1d40d801c00d019140206003940110300400d0102400c1031503600a5200054920031030038200b0500b03005010342c60045007 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 527700341 1250 527699091 527699093
    0x1a0301141c0605131202100e0708070902220311011b150b010504090905010509071205030a05070206070b010e09060a06051509041b02030309100b060702060310030b071805030604 78
    0x60a0500000042c8055140c0c800503605084241c1d40b2005281c111a60502d013800c0b10310042e4880c4040040c41c0751003810f103481600c0c680f1000801104890100001300f01841c6007c4291000f9000100524a0031084400c5040401205070526000d94056149000c801043c000098411001d070920840c3d4a40041420000308661100b07400e4606541500442c4803504500101c40610468010000244c138100101081c044154002c03482a0200000c981c0440c0d1992060b18041c0c00b54a0b0042095008001d03640409102e900a01081d5101504107810b0a245650b91441908240c00410700880d2100400055000420004d5007029042904100c400c1c1801d000c03500320658948062800d1070300090311401070712154084102207212401c030000c0d00924200003900d9078000e43d620629407180400e0319404250314441d40000301c0c001440c941c0b03080c003076500f403203140d42006140300014be0748203000001186950060034458400d0f951055448503403070900e4001e12859030402c50080d400301c42040 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 527701591 1250 527700341 527700379
    0xa060e152d01050d080c01090203030c0f1605032a03101a01030e03030a0e0f01020d2406050909041a0403020610140d02040207150903091d070c020402131a030114 71
    0x1e84041c1c000085c1607507161010f08981c0900a00e00e0000d4151000003400e10701c9210118002580200400035103010381001a200703500c0741c504e4010705605420116110400d00603400d10752503c6100c0111449080c000000000e00741840c1e011821000c40d283e01560203c0034041c6020b2400c020242010416612502c562903681d02004003c5014550344141c0400c06080c204081c0c0b5400c1c2403000250f6940c825440520050040c03920b400e801848101440c0f455030748107010040540348a640c030241000182000c01401140c0a031054400b4402c40c51100100c142941c507182c030641c06900204600d040000d504a80003a80f40c3c088200c02c0380705c0590840c96030300e06500041094048034056150b031034900b014140350610b0000102c400f450300e4100d10401d40c004000a0840341e20114904808100b105e0841040404842007800204000e100d44014070701580545000c40a161000302000d4961803401d001110034034015447c13900110040212001c00219180b00038000e9807411044901540c80f0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 527702841 1250 527701591 527701609
    0x10b13080a0c140f150a030e06130b04140f0c0a171f14011d160806150417060a060803120411180112140c01020a060e152d0105 56
    0x5000f44a2880300c401c14030380d5542010841e4201c028103200d00c851014007445c20981c0101802c0c0042414858018180d44000c01c07010b00c51044072a001140b01c0455036083c6509000910032110705d1203540c14102c0426081160180b103208030307802011a0304004d0300300801e00e80380381e01c0258800561490046000c201107110078681c800c2d80c04400c14520500701010191181c003000140b0a15203100000d031814100b0380100b941c039002108540c40c1d880c0d4040c1c01d0415503079681584003007100e400226000c6e04040e44c400074072048244403181030a0b101c540c0c416402c0b9501d81c00012030303840102070041c0780c0c40e2031041800810003c030007145419420403409100000c001e0020340000700080c84948152501485240303401405c404030030382503840c1e46410001400e045d0003590102040950440f40d15000119120403400503001002e09e0400c613903501340604243d40340101d09005a0914000a0002000c0e50780242c0580611480c2d100004802e00070841011204030b0711407001100411a5440e20805 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 527704091 1250 527702841 527702849
    0xf0b0d0b060409090302150f10151710030201140415050c03040e04060c110109020a05040c03021608211b0c0c10230309030f160b010b13080a0c 63
    0x20400d66240c0c400078065000d41e6000c0c444450400080d08201503000c20040d40542d40600308401ca6141d40264001520040b40c1e02104828441000e01010780403000f84c0c80c00d50601c0ca0b09a18041842c200445141815180d412001c0b403084002d008660700440056051510918002d080c50b00c2c2201c03101448103000b2401c4180200010049082e000910844016000780c905100147c10140781110060030041c22140c0000d000150075144014107004070a1000d80060805400e030381403000f08002000744107080c1c818103500308401d44841210503500302046006082d52a00c1c1c40f845403600c0c541c8481401c0581c140c520490400c0020003003c10111103100840301b060703485201f0102c07220320b4000d050410942c09902984000718841c0c0c000c02c0710b0041000456014040302219102928501050303803c01e556400c21f0212001410b00c09010b00440d404080d0020006003180e164051180401e1300105110140050308601003800c256084005000b03010003414009500d1300c82400002250107 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 527705341 1250 527704091 527704117
    0x182406030a0e101401050f010e1f170a0e06071b030f0504031a01080f030901090e04081306050c010c090305150405030c0106090e1209090f090a120c0203070f0b 70
    0x208014114200684a0f05040481003009504c0081d03404d0304121509110b803c0c03040d04c2141214070345501c10007c1e40b40441000e0a50320026590103040d00a041410131240c0401034503255075510f100509801718015941c200002803209050180a400e1000c014020024414440d038040c80340500080051000d503010b2078862802d0b07407900d1085500f4031455001516106000c010003c503813a612864a0490b2904800c88420900c00c004040d124003640011501241000c181004101810a6456801440344084a1614000403020294900d07075412800005501003180d45a400c4240b00300c21500c60745080100c6040d145694460390b80d240d40145480e40010400440e0800504105586070001c0005c000d1102c2519201504020214014130200700e00c80c4544a94028032a40c1c102c46182c200035021042e980e40780c0d808640b500f403029000c0281d901c6600c0124000c544000d02d10600714400e5503507040c2410442c0109031520300c05410418074803500342010020b2805490881e003485291030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 527706591 1250 527705341 527705351
    0x50108070312170708090d11031c090501020a051b060408091020030901030f0204080d181a0309010e06240111150f0709030c06120b182406030a 63
    0x704044582a8800707901008101c0d103481401005a048031000d80b09402c0c6d0303012a285041007403800c40d041458921042400c3d001000b400d0f1003610700664400c0f020102200110f0780301c1d025a00d41c1e08a9101b031140c100010320104990340801c4446410111240540307004007001d0420762030380031582c414403170b2040c49800c8020010680074002c42030001d0449414002d40028841c090505481e9400484c0207400a031506504428408282c400d55007a61400801003102200010040c6c410842c0350100401c107141da4500014260baa4002211800209060203a140e05042094509640c26400000b035036803c40d04c1001000020211002c01d80101c0010504003e41c0040040c0c4603040f241c5003410041c01110150740c40400d85591a60145c200141102655030b03558408581c0400c2d41c0c08014092144440100a0144102c04060015210103400142c00c400500021501100108040024030b845000c00c2200110031030001c0740c1404610859045201c103c0c00030391107200007018448000d5407a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 527707841 1250 527706591 527706623
    0xb07051e0f0615120f01020405030f061b0c0a06061e06050c0607080c0d0509010b12120a051309090c15051303060f060e0903070209130b0703240b09040c030501080703 73
    0x1c5030200b4038040c0045da0007640b04000c006000c1d44c800d009150003403140304e1411112003000905580711b4040580070301001043d01c43e422859030721272072441e0b10710f02ca00b06038440860700f640f00d984018090610240074414001e10081c07038240081d070080c0280030044c8036100c191070021443c150b1100462401c0490703946c40e0088000c0c0c60081c2044404071b146010b0401220440c158442140880101c2c0d21164010200c4a41d80da1440d030800300e60f4100e00140701d503220142c000c4000d0100c4d6040070b02890011a00c80031800c0c2258a80d1f07200307036100c07000c54400304803942008080643c20099803424528150b036000880c03041e0303441480002c3c40650b84044401510078158840c2004d024850844c3c8050b0600c6090700b03030b50340c0000000ba881207118030041003160000800c081a1a54040e6480c000c0d903840810980c001c0c00d00c181844400344241d982840d03020040900034003e440f62894071b540301c010400034001200d407120700d58814140703087c3c010f00c20076100007010402ca90b403100b685020f01411b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 527709091 1250 527707841 527707849
    0xe0a0602190309090c0c060614061e070b090a0c1e03020d0c08070618090506150c0111041d010510090314071e06080a0c0f0c0203070b07051e0f0615 65
    0x380d800100c0d614582140b08203001d5201b00d1505c039244c0524020f110b01510303818100440300403501110f0380303c002000400720140c0a5040c00034140f0400c0a090701301031440d02c465414000498044445d604005000c504212503212800068203241d10750080b0700d10391820112420045010181c42480300600740010002d101d002031020b010040140d0341060303915140542a000c030f200c1c0b844180d603102c840100303406040c3d11070b03140702e030388001c0408070401802c01d40c41c2050790011705c050303401c0d541311207104c10043c1c200c0c4011f0004148011004e10b0040b41c0708540900c4200c1070300101d11a90448881ca00e1180d480850032090365000034519060b5400702d030244e458400c140e4000c1170300060101c1c911481d070500496a0040385e8103520344030300359030b10500110f085441d0302d003031000400c1c1c0326803841161910400c0440001840601100c0c0702a41ba00601c140e02d0b0000d000440b95980030f10721500441005400c80c0c1c860b08200001040d060a85d9042c00b40c55900040c001604041d440034200190303030f9 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 527710341 1250 527709091 527709107
    0xc0c12020a080d05090a0608090604020f040f051602070611031218010509010207021002010c140904090203031c150608070315170a0c0f03171605061005010e0a06021903 74
    0x101c400200c50802110800c0030f1310b035420075002580325800c03032880001c244d80100c80c0c0510415240d40078001e00e03590355080002e4101740b52626900305582c2c615480c013180d014030845005a04812280c165400c0c0c0031002440e0541b903030008810465035541ca07d1240f45c00105460901599540e544020b40d1344491a03040310001c9505008607600704010b02001103419401007201e00c2c0240c0d61041c403804084001d80c00d9400c032040e00b10020300d060410310400001d100103800b1082005001040c0700034a030300040e2035030b000740f8071049000c500710351002448042c0d885480f02c2441405030b91403032180380c040c010703003010740c003c02040c10b0645a800780c42840c80321f0403c2d240508040c1c4000652110440300f100d07511f01d400cc0c0e00316507182000c2c101264262296800707004a0354856000c5d45500007044054110703400800080c0036000c103444410000840034003402d17104e48031941c5003480151800d40010100c81000740c42500039108041e0a00040340c1c0402c0d4500b00700040190628500301c0341c46c080710810 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 527711591 1250 527710341 527710349
    0xe0405090f0a120314190c0905010813060f1a0a12201f020d02060a1505010c0812130605060d0308040f1506090b090c0c0303010501080a020c060703020a0f0c0c12020a 73
    0x1036900c0701003103111b8406015003100c581c1058000c00c0002102102a00c16401d54083c030340c0810700e07101c002013400080e01e900b000b0062045101042040305000e40201740c6071500e402c0d0b445811408c40044071403c2c01c80b0fa800013803c003100c500301300e0011600c0f039009001743c2205480c140158103100b24100d48640700d07902108407110760040701c41b180e000f10007034279440000c403214014003404002c90004c0450b4040d840614600c1400d015030385103003000648445400c0358085074a54002c0c005410b18a5071580b426208145a0310940048840382c03416004449004103528807030b1078104e0444003c243d204921660180d440b0860b0701c8040442d0401c00c42441851481010081c2840c00214040f0300301d400201d22500180c2d00b15070740e5190f00b0440400c5002c1c84000034a9540184010452036105640403a00807400c10001407900c03100c0d1104504000d0100c40c1e40000c83d40010340c8002090340315000c10f00003091031500e021546001d9036500a204168070585ca00814013011080c103554440038510010 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 527712841 1250 527711591 527711621
    0x6070b0a02040b0f120f1015020c03030a050c06130b040b130b070f090608041709060c010f02090f12070612150305070f080a0506010b030c0403060c0e0405090f0a1203 73
    0x240000b44c22126241d8001e014072802a20001c0100303015131000c1da01c0c40c1c041d0400c4d4204004079410044044081c000c40b01c6448210b1140d1840102152010300051880c2e000613640d480d82d07420b035510128500300c40501036090f0450910032400106804001c82a0802e42c4040c0203031454503100084084a0308844000e0b00310b40c80354040c1710b07440781c21000b154105803103615030050080d40c1d80c0e41030381c42c40000c0302c000d03151005189426822506400040481c0302c8001c100a040c45802c20f8030714215081c0144034141d0340d03400103c2004e180340c030507484003121104403980c42202650b200c080ea100c2d0305520442c810b20441e0948110b102c40180c000047c05d5400103468103a0300d039a418403682d21300ca54843c8041000c03a401001c01c5225000c5040000305400c000205490791030580d10642d9540b00070800c160600c0d0520003c00020001d004180071a5060f9440258445040d0104412510042c10451040e4004490b0340c0342c07902d011500810040d04140e50610003c0841c10640182a10b07005040007 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 527714091 1250 527712841 527712847
    0xb0607080a03060e162f030304060e060a0203070c03110309040f061a030c0a1d040e0313060e130b0604080706080a0f1422050313060201140606070b0a02040b 69
    0x8616410390118048030600b020b0000380d0f031180a1165502040b171551580050381500003110307440c01800c0f04809400d100011a080c070b102c3d0010746800c603001543c003100d03410384480351030304101810000d098000c00751003001c500d5800c1c551809001403010300e03802420b020200c203505c44030280c10310507140040b502030810310081c0c071011803140007881c09018100c01550307021942d59010329000241d91184141d000707203d00e00114018141c07901001260107405400612109809580715400741706180844840150303280c588256460203100c0040d00800104603400354001060750fa078400455101001140000f241038007a40400c8031449941c03c60105480b5000380001c40320f510a804500c240c0201400304000700d1248101c40684100d840e6410300e00c0010800b09054122900c0c4000700d050b4488501403141d20165142c90a54100009020b03401844a01c10022590280905110b11203200401050352600600080c22400740500280644410030f00007044021141e046801078010f40103a103403 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 527715341 1250 527714091 527714107
    0x603020a11071a0f1c05061206090618120a020d02060a0204050a2d030b401a0405010504060e0610090506030106050a0f0e070906080a0b060708 63
    0xa5881909508001500088050200d000118140080d50400e018100d0f0040511204a945400c070074084080d101c010407103e6a150307514402003800301410381c0082060300e003100800c000607070481c102e480d154102e6400c105060f040801e080c0d92200502c054444000180809a07140941d01d084d03051490200141030f00803039400052034810628581e080326980d9549003164010b03406540305254105401c081c0600005c2c0740c10003640301403001d440c007141d5681020340124030708020035402a02c00114130f0050000040207a848404400c00010500090a80c10300e44410703103540c2e0024010200b219100c0e03c030200011103041484124420340849a0746c100303400c1140c0241424ae40881b100d034078080c6003e01d03005010442912403e856542035030007074900240180900402011540c0c0343d566480040f503036036110107000e00a821495902b42800e800c1962100808002900328024004400c07000c1108a0b8882d80065010400c06004104803d0780c0c0c001c80c2c018003461200801c0c440000c20300300 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 527716591 1250 527715341 527715347
    0xd02121911061c15050d20010203040810020304080f030a0c03050a09021315030b01080d0201060906060f0e0a1a041d060a140112020f190f05070803181c09051509010c11090106 77
    0x1c0145c0340c1c0f01044481f0003040b1030040e030381ca1003284a6046107410080d012030064060364080c5134454001d030450340c038081c1540c0d1010004e03841110301a541c6643d030111030001e540d25206880d4042c081c00b00400440c4102e4001540101140c812100c01a80354494002c1d200c182c0c2c407011005550088200c4c246c0e584490042c0c0d11a180010964010340c644280007035a19841e000f000103c0380700d0b4454450103800d00390200c40041c0c0c0c80040a400caa262000001e180c0035039512011001c003502c0200da00c41d420303c40d1007000c0c0360070308414406030300080003070100c560750751740540341119035a00509100480302801a5003c10308480d50794401840411550401006d0f40b0080c045c104480b000f080b407809150700c0540d600000136030b40c040044c0e001c1c09040006100c2c8002140c0044d4071250b00521035030b85085061a011803002e14503041e019000704e102d0841d030412001005040200c800c00e48040060b0250b0000703000310f1800504001110b81c02c08240320740c0648403d0040300107059000d0719a1590009 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 527717841 1250 527716591 527716613
    0x50903030121020d0b092d0c040510060f02010b0d060603050c10140c120304060c1202040b0f0711030604141006050f0d02121911061c15050d 62
    0x4001c850159410b04480c800007001400da0a03402070109141c43c0d016290398107644d000409402092080010401c0e541e450328044202c5000c40800c01c20745400000200c5003003000090842e40900e003018180002e20022190040c10356550346403452030302c5150f00e812409030480046c425080815007010000b8807290b60019007e99014904503400240010103200e0040c092410382c800040502c20030081501000d40185950216030045440e4545551041080c50744142d07800ca0301c143c4d9078604a4602030308039002030320400c4119011402d00e0b103407000300a0b1521804102c0300701d80e08009100b45c104022103c80e0308090001074101d031154985440c0400c0020181c0511403c01e01c03d4103607109200b121070064505985001c0c04c000c00d65070003082400340d10035014408aa02c03422150100c02054010007005001d01480c601072440b0304060305240d070940c06500d803540e02602e0204101c1442c1e9244051031a000d07451800009103040d11610014040040c40c2c03c0568000c0740c80c07142c0d80c00e03c04c4810750 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 527719091 1250 527717841 527717849
    0x1a04060902011b0b04110d0203030d06081e0a02040c031b080103110d030c02060705030c0f0d090906030b060d1104110705010b010c050d05210106030e010b090709180f0509030301 78
    0x80d0040c24001c2e00400e064480c6820001014a80c0c20380020740003074040c0b0200481ba4402500e10850b0b070f2540d43c0001d045800159551340d1041d03039000d0412100d0400c020302444410303480c2c6804a071302041c00619032682d41419000c0e001355100c10100726490710035448580324011140e1000d00c0508101c000900e0030f0428401554104407070b01c503a11a914102d07112040156141d103070804104900ea01748002e0303030085101940c0f14042440a0814100140140c440d6005080068950f170342c0210009014190990412001e01e031400d4400e200040070001c040740c010b5003c07140c040d1414201d1a140c02084025804188c0140c00d12020b103a590703a9400191448510030402403060b11140742c01111040390a44010307015500810620200d00c0c0900001e00000c620503030a8405a00030390040d600c0c0380c00c20b0784a00d00080d518100c405503034400f881808400722080b2141d20385424450401400312029000e840301c2c0401588040c040041c0c1a44068508584d00f602404249060203403551203400903c6 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 527720341 1250 527719091 527719097
    0x120905060412020f010504150311070606060216090203072705060c0304210314071a010b030118050105010905041e090f021e1008090c0d060c030c020601120602071a0406090201 77
    0x9920200350b018030155001c0d102d4120f1817448c1402007840403030192004e1b414a0120600c00c21191005c41c43c5801520007800b0290010f114000548110004090080c1e2008061500c10700900844a0740a14140e0240421001200500c50311305003440c1e51a40341e9000c25845040055850380f10301000c4041c10440f5000781c4c00c52408101b20300916041042c0c044018001000c20080c0010b802c003100151100070b0040680e55400390340342d03203a200200000e0300b081d90108004401041405400c0000b0607001c8001e28042c05107515041c0064102c1c6000d0280c02d10407030312103020803412038501204412030300000c181030140c1502810103410021100f10180e004942200414503110000c200d01c108241014182d41581c44904000b2614640050200302d0f583c0644000d41c3e50554401000c03010540c018980018170ba940c241014040700c04004101e4150b400c1040100019429010201c403040d03000600580e640c0d2840c0340911241101c1042c407840000c0100030f01013800f505034459900ca03071003a2 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 527721591 1250 527720341 527720359
    0x705010e01051219181502031b0a17070c0c0509061207140a170a02010509040b04020a0e0a050d02010207030807060219090905013002040e01020d0e010b0109060c12090506041202 78
    0x12446402c01c141700b00303000e40034800c0146688081030040e4020b45e07001c858048441e12a0122142c3c0909035400300142c200007607801401c002c00f0254109006800c10389605204a10500b291b4034400059046d10829104414600004070341d51a51070240010700d0601d02a144415160412040e40e40b9000e103141d0700814500340045960700042c1c004024112092000300600340031540111200c0c1d11014072641c00544036082154152524005441c0e01025903c40749003490304502409800020fa070f0246104621038503040c3d0151340c01040c0c0c0801c0c2d81c0c0104406603a4000d50034520040e1140000740d403c0c42c4060383c00c4012190380103050a052381c85101c000c0c0b0050f40d8642200d40110004920f10826591020320128914460b4090070505407024002050703220003550000d0032600003121810443d5255000301d080b411084c0b0800e041c8040c2400d206014500f0a80000e24009203201700501100c1005031a1000078044c8503038000400303005203103680d2603840b08070300d90680500d1035040340100e04038 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 527722841 1250 527721591 527721611
    0x90b01060203120112060207020907030506040b150406030513170d0c0203031504090c080709060503010e0615060c0c0904030309050118031b0804120f0b16020705010e01051219 77
    0x2004543c03501e6070b03414061000303908204030800c8200c81640203e0b503081d030800000c001a01c6250090380b10f640162800155490000305000a0b00c8845660f980708110b60352404803075004110644007518083d01d4001007a0303a9100d90a81c0c05c12880c20043c0c00140040088070715100345200a14031000350300c609110b200c03034040c02a42d41e400150b40080741c8030b0345a031420040341420350001004502443c0d18414050703680301700609161f865040901c10a03240d06042c0714508090003005c030250b210500901c01403800c01180071071040d061514a1040b507000582844016040140c00c05540000340030b480d5600701498003400a255800c0c04a444d5420b00c2c224986a01c80b00800c4440550140c075090040342010382e0b6001d0941151800322030906090001140340980d6003440c9002030301c03400c00080860003904113000340400c000c180c800800b4200081c41d075903981c04900201185d00a080400545501e5001030300c03903000e030030b0074501000000403c11904003000341c084c2280c004a204104469004 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 527724091 1250 527722841 527722843
    0x1092d0b1b010c08041101120c0306051c02090601030914030309030a120b011709152a0f18011e1d062b0204080a0303050103020108010f080c0103111c090b010602 71
    0x201c00460208510100260106d4910000780502c2201407601c0d0300c440005182c0c0750f045451180902d000030365140801e00c103038101428400e8440c0804410002105081d0340000d4043c0320003082c49040540704d9014500700f10500c00b00c200500e054030141c80e180c2c640f62000a6603500404001000280b10b014101c064440500c05c0138603a850680d919460b011303565070382e1000d2840144c80f080c1c0c0e40c46044071000c404d811120481d03010341c6030380b092800b038000e400d400d003900a443c040c865420041c0c1000f500885080e032030115004810740b40c8403c22684107560040c3c0301e01e0015901448000002c001d0340c540c8035804071a0f046840d140e2044240b00440038406d204944c00b4101001ca0600d141c0c45060b01c0240b580c04010300e0b001e800c1302c0301625141e02c5107009410f200d07001da003c4000c2515080140119a004502c95000d090310f1081188004c0c507003643c080c0e580d81c0711045a0305042c0d91300300380e0450328902012541e105400d824082800030459124000030042c046003a5040640000003003581c500c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 527725341 1250 527724091 527724101
    0x90b0406120b01110d0e1206091b150304060f270605061f021c080402130b0d02280509060d1205271e01092d0b1b01 51
    0xd480e5540100801116100c04010051825598140a00e40100c03440035070341002a005d00604075590750741720382d0f2401c007444503c125410101441d90080c90800040c0c04000486038403111480001034000760005003c180c002d080944203100310300d00001000180982e40e001411840c40d111030401655400b054420302041c80f0501c0046021301c0f070074400001c90b04d1500f050b500100014848113201c1220b00c18001c104440a8145000d42c004030410684052181900303041c6104509000c04580340560000d01408010400d40d5100d503600c4c0081009911840340c194202a03020300001e03580c1d00221001d401e081e030014100510001403500110b0941029400341e4011500075100c9082d00c0c10665441442d034440c4070422040003020300003900d40700d421584c000030300f1004048000e040d2030355009020300c50905c4c0c02100c000211150072140c007a603100e01d203030041b40c894a8140e0852061001d04503034100d6444643c0b042440001d2000c102481c0c18401840381c21282d10b00342c000017400c0190b59082c0c0d2 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 527726591 1250 527725341 527725349
    0x1419141506130b1201090b0108010e150405011401091d240c0706091209050105070c061d03030c0102040801270308070e060714190b01050f1207060201020703090b04 72
    0x403859202040850070a0700d000c081ca03a0019201140703103110100821100b41401c5242003807a916212400d003805241c11a59001d40200e030021b00148070800141c1d65500170a407070001a120891002506000b0290301c06100700703915400560103540c3d1010b01d04050101e0140c042e4103000e0021054485d1040024011207050ba820b0054201060705030f90002848002065682451010014040021568414001c10b0341c4035149032654070800307950041081400c0d40019047c80810006040400c100044030b0041380c1680c41d0a2a1516010454443d108004085070390548000f0a403203140c001706401520640314448002c018103100540070842c00c58402c01c0603074040c0c03492080d02f000310348070b00111980040103040207036880c0741007004690a644015000d4950522007101489048418820312456140111000510b10501d458076412491706100b01841201d01340b01c0c0304026100d41c200d403130400080030b0654a060f80d4801c8041d001c5d41c80a41d044000401d510300110b101501072050b14265 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 527727841 1250 527726591 527726623
    0x7020d030e0705190b0412060f02090d020f24031501090f0e0703020912060f0106080705090d0203070801140f060a03120c1407170c090601080f04141914 67
    0x11a00d0b1005008600b00c8055400b103130f42d0750f002c401051598414000b0001418040c14080a24040341440c004440390030310a820107a00412503c032542e55000c1000109580407034a10090000b51000078080051a8200c11503040b01c0140c203004603e03158018501c500c11359001e82840c40062001111641480c3c0107040106c20070680c103020240001c90070076482440d9082c0140b6004d0082c1c00240c0030f0822081c4440d107a406a4200501aa06007403624010000c90038090200d08001d500075015005000805001d41c002120710015541c0802c004001885400020070110000b10112108424211030980d000410000821400d0819540c1d9108803900201c40d02500c0310000012030300c00c00c0c002e1094800600da2110054891401d11100e001080c503000400c882d60602e07203d603030400c22107030607041c800c0085404200ca107980007809698400440c0c1d20004a6642d24902105030141c907203241c071428400c0c44d82080300484500541d004042c000e505c1000e49040600c04556601c0da804041040 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 527729091 1250 527727841 527727853
    0x9011508120307050a12020d021c1a06070305070b0c030601080708040503040902090f100302040602070906140906060c150f06040c12020a12050405070e160507110604120b07020d030e 80
    0xc0c403849000900300905082c60b0492450406c00c1000381070703801031000800542c0d1b001500d0056030b154440020801c0c10502402d01140c0e5502044000030021070a0060040701c00041d9041058407440807241d5039580802c1d80101da0030130340c50300160781d0400c45050b030109000780e0104820901410b050781c41140c3c8040114a0700b414075001c1e00c080d410045050b5041440b850440200d07980398550445104c3c101e981c0140c4652a2000081c43d00c1c03c2c41e444108160301c0c0500600c070410312800c010014050070385815005456110200340b0307074800c3c5c034800641030190031422905004000c03180f034010007000c8210aa02d4a8840170041110808441c0c200811000c00e0030803001000e54002d4081d28030f6070708000300000315008010082e600c080350101c840ea0010700023880340c0b41510f94180d81103030700c141031052040b0032814007034603500c1031160140c9680314040c0750b4512940c5000480d00601700c0007150300b00c0c0022500d0b24102d01d04090720b41d2009805500643c400c1c05220b0720442281c1c1c00030300c004000e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 527730341 1250 527729091 527729101
    0x905010f050d0b0a0c09081009060b0d05030d050903040f0f090c03022a0309030a1506060534061409010f05070c110301020f0406020d0e0901050a05061c05090115081203 74
    0x5c080b8404440709010056100040d049024000c81c1918803c45a021403405541d1500c170b0103d0710344000ea40d203d03004a540d00301c0842c10010542d0308405105200003140c0d112600402c1ca58001c80d40040550b50030310b280070170b10f48505100d400c11940200d00c2402a54003c1000303400303070b0041000000f000810007a154100302c515030144508888014282ea02e02940e003004642803000c0c450f81518203a032401d4105e00c0c1c4020611900e402807450346030103401c01c88000c0c0391800b0890860342d6520107220380550440c024014440000e40c1c070307074800e408100c81c0045c0071030100d040800301c4124035654601002a2090b801c240600d42c807508043d40c80001400b030a54a00301d14184441050f6015035081c484801041071080c0284040e00f100e400510140c4c40c1000014089001403440c240078194100041059031031b042c0d100341c240c2e0003c0300c2d040d4079100710644084400c5045848200c5a509190034080421011b5115242040d014012110300903206c8900035521009080c1400001400b040010 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 527731591 1250 527730341 527730361
    0x30124030606082403030d200403020307150e040f0b01030b0108101a0d09030306080f07030b07080a0e250b03011203030c051b0d0801090507080103021908070905010f050d0b 76
    0x4d00000318120f484506450500b012074550741108130001002c90351440a02542000c048000014101200d0711500c0d140c255408203498501e02c0c4280880d000b284541c04000b107004512002c40004090301c1003184c42404005a00545010001e050102c1d18103903140c0107a500c2a05240e110b03d194050f5515820302e05002d0350b100901c4207209080f403110501003805000362500501107054002c3c2c0e00803400b00d0074451018103028405c580a00d03698800780342000000d41040026a005c3c0700b50074900c056035600c0c0c1241c0083e04039042014040e008014065a0b0510103a5400208540c64040c402c0a15260f58908034a84400c0c0501110102110f01490019100c1e03005244606082e14042d070400000c1c40181d070360040b07914aa07070380a401500380801d16a61102c079860040c404154144074904200d078025100310010300001e4000c20040e106904180f208002c09030007090f00328100c07000b090390f07003da07800184000e0043c065460424440043d96250440862003d1900141e0240442c8c480c24200 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 527732841 1250 527731591 527731621
    0x1905060607170a1202030108030301080105010b03070e0f06040b07120908240402010c3005070f11190f03150606050409020c07090207080702010f020d140d1103012403060608 76
    0x2500401500c4c1981c0c070042c41d4130340055402440b0100045450303504003c8c0b45425200c058104000c880d80134020440c0550b8410700c078184d04c02080d154180b04019200200c6c4151240e504900541c003400614102005041c100010144e6129039580c00784c0350b110081551180100c00f03100724101c040103080b120740c240100710141c10501c1410800356103280ba5031a00c240c4051030b808484d00e01c074280b8104501c0070001042103102030941c940342c0d180042a54503c1c200340301d01c0b031020301403d090041e030700c00035100c11444052002e00849901409a41c0d0b0103c04068031080c0021150500300b0800b05413010514080e2000303499a980300c803428182402c400d80002c1d00a0304510345644141e0f0300001e060801031006150740c5001d041c0d0940e8601940c0000740a0150b089580c8045500003944000724a5200b1400c804404d00b514000e076503420901c0100d4080c0020710760005031030030000000510840721401d614120b0101120100c284849100160111003462240c2c10100c1d1000001802c40581c1a480f = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 527734091 1250 527732841 527732857
    0x71d060f09030319020a03271503240302120105090c06160c090903170609150a15022a0102070302060d020705010c110106050603090a1202070e190506060717 69
    0x89a013880c2a0604603070a0125403107020002d600680d10450505600070241d00c0205c01c429101e45000403441070400b0885081d1061f640c110482d0010354079103e00c203420080b804044482003c440c4809441c1c680e21b90445448128031454119048051007501801400e100d0b00e0307003401030a010003060080c0700269110746011504902c140d0644c0c0009100005140042c100d10a80090100902d2401500315400d50001500d500300b244100001035450464040e0700111802c5c03a081030551180215140382c0032501f101075000e00d080048401c035580011580f941d508140d02591005d030f00700400007400d900303c0c440036005800c0181c080c00981000401480c00c0c179101d0302e0041c03a0011988480c3e003183c40103100c580008d4005038812018074001d0180c403010380000c4904a1850900c80c80701550752800070300040c9107402c4103912041d41402809113030300810029000d100c0f98030740b0440160146800110400741d26181c5004182070742443e0341500c07483d41e400381124480072082140c500158000e10a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 527735341 1250 527734091 527734093
    0xa0915051c0b041109130b06061606060803031f061710090509010b0f0a05060412080708030411011709061306020f0c07150509090406020307170c03071d060f0903 71
    0x204400c0029100c42c40c6070310580c0125507071814082d0344002c02c44008000f411982200840803010030100d4182d984450700701008a034a69614950140d0004810301e00d140b000d407649107404000500c001c00880114440c1d41c84d40000c03121007036030b00c031001a1500300d8014900005c9000ea1822150f91081c01003507005110202900e030072941d134100708402c0da40c081f90000c260f40d4480403200003174100080101e4522804484403000036013401c021581034000d92141c100703409a480041024800764204507424140c0004540743d0380d00d072034101a508002e5400c00b44d4001b401e50302d5401400c070200c80d103150280c04c542c00680302c207841c0c0c005d4040319144021026030394280d0030082254042d800320003c242d003500c44d0300900099032030400c25440c50010309102e0b1050000c1088641a50b039900c111465100e1351140300143c40b51184001114054452904100221810744c10703c010140b40c5800355100384041c2e540c40005e801d01070707001d1200042803281e41d0b8002d4002c0c414004034400e01c101600c80312102038 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 527736591 1250 527735341 527735389
    0x40501020d0e0f0705091b09150406180803070b0a2415110d020d0507030509041416020c0102120d090b1e01080304050a210f050c0a091505 61
    0x11607400d048503411a4024503d62280b0805407021505000040c01001c040b01d041e506440d140342512104081f584003540d801500051180d8999100034010714040000b8140ca0b807550340340c040142c1122082200040040800200080c3c041400011120b815600204054054407040700103c050100801411403885400590004c40403510340c2d04802040c0030308003d20500410040a02400580c02020310710340c20149a48000b03e40004480a03020500d01d00036685109a040844180c041d07400803a1b8081d007071182080c0c4c03000207540300c2d50040c1500c0350030000c11a0428401d83c0d80d0703100c0601c0c6901507001900400c40b5900701d14003901c0003809a0001184054071556603d1600340101e400d0441019080c005190a250309250035001d0300004006529103401c2c01d00080c1040c1c414070810051030524551500d07030100242c155210180e0003a0348020340340e07d514225840d01102c5100e14042d8009000008103000240a480c142e14108108920740c20f0500c1c080c8207220301c3e600001c10601d2044 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 527737841 1250 527736591 527736607
    0x708030601120e01020d0c050304110609030a120f0318030f1b080708071a01080a1b0503030a0201091101030606090308090d050d02060f062718010606050706060504110d0504050102 79
    0x10f0003591403001c01200010f0399622aa629442110007200072030081120074420080001c01c820800c9116103400c981c125160201c64000078605291100020403409c1c901c4842131060b5005182120399a070292401d1103e05000d01c21340703c02503421440070740014100411419584d00909103108151b02a403002001e0760013984501c032707a80e400014208d4010b80000303440340a00600781c41c070069504408500142e1940b402c1c1c089642d805001d14041d01d503a2000c00ca0b90108940c0c8000b0100a2030090162615012036880190081400d2002514003081c0c4001c0c0d6000380d031080c40ba40d0f05484081e12450b41641c150740701d806840d0865401d1b150030a4103c1b0700c3c40c000c01c0c02081041c8014a4a40c010034003850003980d4004101406850075026007980c2040c80c62a88060b00c80803100c52a11110018a540b0f04104510400707200200c04280e5103840d80101301d2503030140040404a0107020300b4001d07542d59406101c11541807000c1060007220030f11030300780e414455030001600107000f41d00241c20302688e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 527739091 1250 527737841 527737877
    0xb0a050615070b041e020604090e030d0e0a0b01090204060207090e0312101503020405011709010b0a12050f03130302090c121518060127030c0323030f0708030601 71
    0x400101650001e105108020802100d207949440c200d407002030003603200c101c03540420008c0c0182d009100115482d040e04074020001041501c56a00d6030041c240200d480700713414140c882c0702d20402603c0c01844803001040541440c000c0b40c0441341550300501891340b4202a041c006e02c880309100045000070061b0351034090120207858000c01181100f1056185041d1051202d41103504800c0c040c10b0042c8401c020581e0010900301480c1030000d00391140703a0326001d0040c01020380340045a4484e0105001154400d02ca650098126114034202d40010303160140d002d41c0c9014200d0088104403107103000340014108600542c0c1c00c410110506410319121120500585000300c03405101054041c0d900401c900c2e1004c510110a002d4000b009110b0601000080c107840fa8180c5810104004400b001c0c242548521840010740d00040c007004090f0300d80c50311803a145489440c2d610704501010300e0240709540401214440e41d2035192152502c103035a42c1b0068107400080c0482e051003118071283e00c000f00 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 527740341 1250 527739091 527739097
    0x10b1c080f0406200a050d08090c100302090301060e090606060c120301090f0506040c080103060510120c0302012003043606080607050906041205010216030305060a120b0a050615 78
    0x2010303403031304c0200a041e5a010a0810400b01e83c2c907030158080c141d000041400414410022041c0e8507094850703036a1001c500b85041c40040c055078001101c0501590b5a65042c0e02030801c0f808101d00078000c665a401c803041c4009002d4400900540201000c12040e1078490000c121601c800002d84241004900901105400c00da01c018074480d110020404110580d1049903072281c0100d40c02c12440e10324241c001d00c40302e0140402800d07207680d90301241110601c00c0b1010001c007180d45030401c41114510340324070b44603040d21040b404100d0a91045030103c29a4600c0180c0107c0000110306140c50500f0054400001c9407241000d155003c2d01404003611415080c501e10341c80b6980819904d1511810510b420402804201000760501c08500c503a524401102e0446110712030103810044503080070343c020321803011a48a43e0002849500805d40c040e001148108011a1541030182c0c0d582903001c800903103a10300400c2400440c00045170b0300d403079130700c5241c00c80c0700030f4681c070128610440d506c501c030782c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 527741591 1250 527740341 527740349
    0x7020a02180402130e0d0c030203040902070c0f0512030f07031713050f0c100c02030709020705070e0708160c032309041109090c0a03180308010602060603010b1c080f04 74
    0x1c0404410042503040920032044482101c410421225006030319564440ca480e600401c1080035404101c424103200b002035a0142840031f00c00c550702c10861900029410300c81c41080003404110000041ca46030007102048a80c8810300914030740418921315690383d0b4000b000c100c06000c4111600b00210940c2c410142c810440a1000c1e400c400f800c1c1001850a0900510b5120551005110552685404240c00c1c005a450300f08080d00c1c10351480060300b0701849410581d016840071a514050180008500044900803d0b00b08203545075a0741c1122a50802c840301c0710700c5600a0b4400d29010307c2080c004c00901d000345404200d0744040200380003c11305400d00b01906141c085500029440d16218403890360894218075450104114041800040002c029a146103004644131003146d0080d000640080528007a1078083c240520b000b405100307003800f0b88801071141c84009240c505051003200c1c06140001c001002c80c8496400200a0701041a42140d00800500000241c94801c2e40a407010b0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 527742841 1250 527741591 527741629
    0x603080705011503050309010f02010f05100f120201210e0a08030a0614030a0b0601090f0b1207030e0a0b0901140f041202071a181e0f030106140907020a02 68
    0x1844030341009402e64a09459408803001250010000030b800001140c2d00f20328282045030115010007801d078014003004020484032818041017018658800ca8590141c0d0300600101030b840d1707240c00904240c1c0d0b1200c0002400302d03003500000c00310321802c1d9605180420141201143d01100c403440d9a09103031130348030b0403181d80c8004001d102010701a4004d1501401964407440075202e141c0c0b000940e1913210500144c80c00e01d484020560591081c00301c24003030b004c0c802a00d10f540795982c4503542d066000c015110906034854000c105410b120b4004c0c40e02d003a0410703000300243d441e2512103410071400500810240d669500311a9590000c4110540c0b00d4001d201c900002c03031a00d82403600308003125640c4a030840d08400024001c1015825100d808944902551030f01c032509080440441000c104071203511400408410005c0da4086142d616480b405450150a40d4529020703d404d85500780100075202090061001072418007016441c0c0c4034809104459842007d600032070542e241400114001c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 527744091 1250 527742841 527742847
    0x11061c060b0901020a02040906110310080d0c1115040f031a0c1603230d0c0201060f05010909050a020d0606081f03320607091a03040203071215060308 66
    0x2a004862040310014092103004514108075032000075243c080641e0020300c180c0d51143c2605c00d02441d07030302c030070005440451030f10b540e0705054405d030310206120b1062102d41e01c100880c03e00305505c03a104090f400382c4e01020071a801d0850800300061056120301260342100140000581d0340000303900c1c0c0c0e005500a10754111520540602107074440300c014036020601d9410002c07410f803500c128202c6101c142d01031818040a034910241458007500701000d041281102040c582442c20660b40414038648058008200003030340c5644055072504903204013400300340746034420840c00341190081030b0700501c248001860b081008100e1012906150003c40c00508a0340030800303480c581016459041850072850865903185551700704442c0b808032041010404074861082031070034040c007503480e00705100c8265807a81c0b13890031000f403200380035100300d010b00201040d02040040c440c90807240266005800740c80c045040644038041e20300c82e98411906180c2c0180c3e00fa0f000312440c422000594415803007140d03 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 527745341 1250 527744091 527744137
    0x10606050d0608071d070e0904120215071e030e0f0102210402090402060a020a060c081902040308031303022b14090a0302010e010c0c121704060503040602071106 71
    0x400c0780e08070b803c44289a80004014040c601900b00c00c0290091a9100e40d4102e68170000221a03950307008458a80144986041c0020444030005a803c03a140039400c56400ca00c88080480c42c54509441c003d000c16070f480217465203801145904010380a19040228001d1080300d0180c2c0742000620f41d5950603540401c0801d000c961700b00321a40000b9488031030680504254000400e0306a0141000307105600000707550000f20300911581d68a6030b00030b00100000c01181401a00d0701c24102c4050003400100503001042c0c000d035100303a8050740d402800103421562520307590540545c00200540552003001c056240c41c032600104011030a1809155092041000b20082d28400304944c500410754420f00c080682a1203a039000070840c0c0d02445d1454848103504e006071200c1c1c080c1203001c0e00ca8201d2100200b9000b80c003c041e022550f1042e26401e840c00042421801d0a000e18007442001030300c10400300d400b040303464001d01481802040b221003420840302c00294140c2c02202919542c90310369203455 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 527746591 1250 527745341 527745367
    0x510051204111c1a25050d09080705100b060c0a020906121c1d03030901080a06050d06020910090e0c030a020f0d050a060906140112060806040b090d0219060f0e01060605 74
    0x10743c00c42c85c3e244040180010304644078141000c0301c8004000c000000c41c0003440c07550341e03404c552801c0f0380100c1102c7d42e80d076260400d00d44964040c289030290380c2c01c0015402d101d0411404903400c1104c010050000e09026500304440000c0140c4103030b42c048814020034039840000c1c40840807020544c0e1042c802c58411000292208400c260310b03d640e001003050701c04203501c000c02101e1540103f4a4072034100d5503100d4411006000b150070103900180850700c01410081d01c0e500a01c3c59060455030820400b5551108540756105800f450344200b2401d070120b46101207100c09142c008102e1070f00503040c40c24071200e1690681007200d040109646503428401550b209100c1c0c3d10180c1060481409a98142282c0c2218210708000d014100b040120340c018903a1401d0f4411006880d007941912028203050400c0101440c0c143c464490324080d105112010034000030342110901194085504503507200e4803400300501d101a4030340a800d40300c264680e83c0070000c2c031648020385100d8888030744401e403c031750074 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 527747841 1250 527746591 527746643
    0x1020316081b19031d0d0201050a0b0a2106050f040b060415050d050f010906270c06050d02070b07180902091c0c09060303090510051204111c 62
    0xd0302c95080442525200c072141801182d88018441c08040301c500d400f100124002c00c00c000d442c80c0081600040c080511501160340d45c13113000184c0c02841a9103580401000300e640c0070285079072000c20030b1401c21050802e40f04d00300821000342c5090000e0319050700c510082e908215406103000800100b00010000c0e540a00c5400c171800b91000c02c00c00c1340171000a0144400c0780134161040b00c43c1381004042201c1080310101141c1703603400078031054250740b030110050030810b003854503014030940d071302d21143d80304402604500f41c2000501140307519001e000e54007540413002c410482a000c00820f40400c0d102031642d405004640d85103046101c4111108440cc195a007041042078010000665540c0d81c1b40c08402d0040c00303071b8070340c2610340fa0545404054003856034001d8030b649007441000028950454000b0041701d000303440d031500560313880700c0444980c410702c0c0c1103d003854a98408200401c12905040c82d50032005032211102000e02440d004200280c00012591020300101800982c00c1e20044 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 527749091 1250 527747841 527747851
    0x100e27030304030f0512060f12011a0109050d030806060325020c01020610060804080a030905070e0a06050a0302240408010f23010308040e071e0f030b0f0f040b040605030102031608 79
    0x105d181801c25100031041101c0024142c188108035001d2206840c0e81c40164400460042c04000c205240700054514018800d120b800d40c08030300425400582070500a039101019541a51840e03803a5407250108100c42d04060b01102d460b15010300110540c00b8195007010b82c04089400800b5003000040009180c01002841c9034080f4487d0346041048982290900fa042a40101a903840c0d500c01a8100c008203030055020381944641a000221805903100d954010410070300107002c0c50303803941c0c18445a0b20451000035080892144030410007003548500001c0d901070b10110134035081e0342c3c1c2d41302030a4480900c0b15030602a5510740c51102070380c141620f091030b1440d603403c04442d0f6255880d0812140210b2142c4070105409500280000d4480c070f144620284401c1e90781100c4890104000f0515500c241403803001c6840c01c0300f00714441c500b0741c14400c880f0000402d0005040e601200303000203880f03800c12441d00161900c2010a182d982800950310801c0001c001a01904004500800703131800501 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 527750341 1250 527749091 527749097
    0xc0c1e02090c0f0d09020d051c0807020a03120b13020301060f03050a06030f0b070306030c0e16030501080c060901180603053405160f03030f0c0503100e27030304030f 73
    0x30a48a484143c1c06031881c012020744c00040920450001c00c5441000407001400b81c056807002d4650b551204c00221400040c50703542e00e50583c0e98aa0070390f89c2c0c804003480900801d04103e41c03071065201030b82180e111040302420481000040062002c181d80007038000a01140e504003061078a258907118035544010804028065a85180c658008203084000040d204003e030b48002920240660004801503500004c44100b85640d60152505203c040ea8054640030072410b1003510140300340aa14141c800840182140c440c6041c1041060760000e040c3c9810300491245044d070242280151000400194034045058603020011501624141500c0e000c0240384002020712903490b0b01c00c07241c1410702410803039034880c07400000e81d6030304070b00000081618121904580403d07a15400180403505090b42c18080420040750503141b0b404112154004020341d18820030240c81e03044801604410324040380e03464a050f488a034440307240c0300302d213209065000000740000c0560008007100303600f1180c6 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 527751591 1250 527750341 527750347
    0x12120307030f0b0901050105130b0301240e3712030f0c0b0106050f040503030304061401060905030a2307060f0e0105070f02090603100e160806040201050d0c0c1e02090c 74
    0x2500003131240c24113005060411201240e0344652503820345284004e000039806150303da40c3c0d0341b41d810300004400810310103000c1800c2d2045100502444d84003641010060040071660001c00e003190301200f412082c001e00c100100c2d144407809506681c03910240c4441c00c2da070304827440b0504014224012a02010741007000c40e071030140100380c1e03038000c0314155101c82c03408a41e1018441c0001500d80100e07044642d00d40000000d10040044992045000140d40c44644200b40c0c1d81760010768075181c0b0f078421507425402c402200000600281003552400405540e00c104400d04803a0b2541740c00500d0308000080381c00c0c91408a80305802a208045042017440d0682c0341c469159550f0b40c480509680090081032108041a05a50705000c1601ca49007c40c0041207035955400d10300b03542d03080b000510300c20100c0854001c50810380119a003480f440c2c040e164107180087c0a81994002e00d013100040040285420f5020000f5442c0302c84030f02104141c092000030710302c0500400c910300740c001d0325840c82c1c24020 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 527752841 1250 527751591 527751611
    0x30e03100f06052814040f0e16090b01090b07020d05070305030d0e0607090611010e0d120b040b06070308151503011701060302010f1d040e060907080a0804050d0212120307030f 77
    0x58000c04e025184040241c200d00840c16020502a1141c1c0e000e00304454200556000051400030b071071510780d6000c040c104c0e20183d2720b1240b281100d18001003140010302403032083c0846401c04004144107440a0440c1c0d00c500d005480d02410301c900c0d034204580a800018a4541c0700c000d81c0610129050f200010744800d007001d400161009800d0f06c100c0f414030031107500d941000300e07003944424001c06220054950391100d1190040c203090b8032400042415151003041c4070b0702c1c10284540c6c20042c07030250038945400520b8400b50b0701d482000f85003003d840030310403c5540340d440d000300d02c660480404030029200d5060030701c0e98001002a0240d4202603140076003c1000d40c1c2e0003c00d001006c801d60410300c1c0803070001740f4149060521044a280c000e03060090502034507800083c024407a000c1d81041c2d40846c1d848452498450802c18805000034006100a011a180088072240500c0c030040c8214001104409403904100c8580d402c0520408040b04004c600341c1c050040780740d0f025100c84100030001030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 527754091 1250 527752841 527752909
    0x21e0106060c12020102130f050a0b0c06040b0402190b1c1b14121501030c0c0305092b12090501170a050603010905070b030108012007030e03100f0605 66
    0x42c4080103440c2c00c40403c0c1484006000794100c40d80c44031141030062203691201c08800f012229445414000d020505c0001951300c3d0340b500b41c5560b40c402d40043e02503511961512880a50068403d82e846808402081e006044450007a001006054212500d6211200b00c00300c5070b031940443c407851a420030201c03182c5008894880c0241c03840a040c82c5545141c1e038115451103004000080340352280150600c8003138080b6400010140d2001d0781c0c140f10002c000ca40450fa400c00d9094001d000c41da0034450210940ba048450b1a010f03107034a0a1811070794129402d080180c4010b15094031211150116120556032286441c0081c003020700b000342c107010a82c10618a4010010034428041d5a580085030169800307400081c2007036001011190b0168542d03030458603582c000c0c81681015031070810140c601c0c062803280d00c0301075800f4100d91030501e1241e440640350a40050041070b494000c45426a0303002483d4481d10504440f140d000282e940c0c105824000000b42400302030001080d245003100d5081d003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 527755341 1250 527754091 527754107
    0xa0b0402040620010b21061b0406110109150209090105060306060f0304020d120915080408040603050402040b0402040902090f060304081e09030a0305090933011101020a021e010606 79
    0x240007842c40450303504200598018000c2504030340c6d0008503004140d84c5a80d07103210101244520105071a000d440d440c00c1404100454040c3c2034039100c00340020840316010ba0302c285442e07150300b4004504048144ea0f4a0011403c001285501941c04207003846942003410700307036016103401c2e14051301c1e5007800343c00905180190100c1c11045c180020000e42103440d0030040c01c48050703000c0b402c040140301c808005000c08606010b0070251046090604101510403001c0c82d0203242c000310990700c0c19003000400c8003d040010001d0b41c200d51624081d02141d00d40384010001840b1050700146c480340004100020381441109540c400c0a0900034040400ca010040350740c2c02006450018005414603d1201c02e03004038038103030740e01d4040e00032140241031300b000041094107001c80d0300030000d0b65001924240c0b503680c007607581305070014403a02c6903004040302000e810040c41410172070040300c41041071500f60fa1041c0326101c0142c1220612030348031900800482c05c0e000e2100024054a4105980100061 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 527756591 1250 527755341 527755367
    0x711010219050309010c170a150909030e0306100e01050909150a020a02070902041805040309080307050304140916030c0201200705012003060405041514100b0406020705040c050c030c01050a0b04020406 88
    0xe5270716442480b29a502d07500510040410440a0140d9582820050702d00c0c0c0107248104c0c000d010b0b040004060320040450340082e602c4103044002507908042c14030503840c200030072001c92846003112410241c04c0b8810010310031080c0302d401583e12111400000d08042150b882400c041d40180800e204c07400c005800350130488141c0c20001220707a100d003022a08800e440d8845846408001210810700070080000d0040d901803408c8180500c08407424000307041c10032100303402800350185072650540c7c840c3c1c0103400c011026100100c1c5000147c082902241c04102090360361800015a602c1000b42c28011503105c441240c0440f0f0000081e645d0440c55444020300407072044d641d90000a04201c4d4044002c81c038010405000c105020074520301b1510454242e5040910b054107000024080600404807401c0d5401c9034040c00c062440c1c0414000178155000030707102840420300ca020600340341000034005042c00c04c0d0020078582051000c02046907109a10203002327600420003030107116041070428080d2 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 527757841 1250 527756591 527756611
    0x5040b0610111924021201050f060a030e0115090e060601050301080706110304031403030a290409050304050d030504060e030c01090302090a1413110f090711010219050309010c17 78
    0x1040303079141c0030f42811071146a0b40d500c203040d4843c041304034050b0350140005050040c0070300c0903a601d0b20100210400c0c0303800b03d242e0091041081802c444e02c260030040d40341030120000f04461266542d40d1590580d5034110000440d95004218210103040000745d030098002e0038410726550500305200d4aa0765103014080c18010310000d00041010104120b400179500650071a483c40d200c40c44894a9034425190000c00d181002000f080640f50500c540c09400404551203480103441000d100180016510554190106000001d010b440e840c0c0c10402c0c642c800c4c2ea609546030708120001e09288040300849009500081400300140d8012406c80b0559404880603500da0380d0701d4401001500c40380c903402009901d411b0a104000141c07082280c415031103080700703401072400d00040c0300d52070081e8200e03554007503064030220719024001d0200807201c4020400240c40c0202d281c01030100d40c0c6404a0900008100004002e0385031021302c281d0b00035503100e10745200b41c400d4041d80c01c0f41020016009440c1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 527759091 1250 527757841 527757883
    0x605121515090402221b0806030705010503150301060305010203091501061701140d0c03030e1315060c031106150108010801090c060f0e031f0513050d03150905040b061011 75
    0x250200400300d164440c0c81703448042c80103203030304028083c40d1440380b801600459880c80c0850058640890010260f0f001a9511405c5988002603040045c654070031480d0903550b00c02c0c0110106000303000039886005100e00401c19204070001d40051768038140d03c008204100c0e48860300c00241d50100c958110760010800310110911480001c0c090080700400074544c20540900204060b0401d1078182800300491306100c0a1900d01c01510070b4030400342102c0c05001c1d18070021b105450092141c40202806850601d884000c0341c1c1e0603620b8070100356500c445007170103074403003204540c0d00c00415805072080400078042e079a0a50f0300d1030428403a500600c1d0600403009200001c803840345100c8021540001c2c00ca07008040d0b41d14200728644d4046040b14003c6040c0320000c0d12181d2004009064198003800603c0c591220034822001040100c1c0170f540b500c078403100001202e1196009541c0524019100031400d07042c0300c030800200c181c0c1d42c0c10003c1030011403480340d0001d000100d01040c8801d096410300c6030b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 527760341 1250 527759091 527759119
    0xf0604030f0e0603040f0c09060308040306020a0e09090f1002090d02010e01021002070813120c030b04060b060a02060702100e2d03040e04110307050f0111010605121515090402 77
    0x24000300c082e101107800c00c0c404410030040c80405924000d090340140c100703004464403119010180d420728040034146a40400c810000121070381c0c02006011110310703203c8101904d11001030480034065524040715400409140f42003c000c0c401d80d0f000359a4510f04510700070200002c1040303c8040c4401a0502081c1c40140303501da4001d00401010b011051700465698a1501d8280340c0f680101c4801220b134200a20089400c01c83c1d210803214444d044000344504614590380d036090f00300010000c58101d5110344404005131a168080c021048168019010344c5c07400003002072510304100307540c1001d00d040c420021780080000c03c04078800c0503c00c2c0c0c1d0300e500c05841030002020a031500d084008034400044c0000760031001101050040384078500b04074580302080c081641d9110f9501515510210f036640d80216036008144080e08022501d001155044d030750f8000031603400ca808246841c5400c003607015a240c0388481c01440c1c2c01070703001203807145528007400030908071000200001c1c01040070a002d04 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 527761591 1250 527760341 527760347
    0x60424091a0d0e0303070c060509150f07050702030d03060905061e010507050a0804080a0309080d0203190e0d08091314060105160605040302070e01080f06150a090906060807080f0604030f 82
    0x80140d00c0300f0801c580d44d030f0402076001808201c1400301510003514201c041540b1302004036a121060501c600d500a058442e014803905036000900f001c0140a0104141001601d00740902000c0440d5514001407152520082074152003000f000c041c82030000040300c0400841a51718992a18020710b0405d1b00d031400e51070b2081c54401c1004c4043d104c07820200c0c000510210001d07108007014860755500c41000e543c0d1075003e070344040071000c03240584c0003070080340b440740b10b2035601051842c150b2501e400601107800c0412090ba8002c0e4042c1c1e19030070001900c034540d0801d007039202031a421210f400c120b49100c0144196118002a12980c10030200041149524402e40800c4c4030044d00700004001904040c60081d607500f070b03540302d03061514420100004080801156000a450f4031101512183e5100c240c0916411120003800d42d100403884804903140229200305c03d00c1d684105000107945044c80c94040c5400c2c0c05138014541ea03480b6005000c489030000c00d039181c101c1d0345402d01c41c00c01080b204041d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 527762841 1250 527761591 527761601
    0x10320220f050a0c0e01020d0f0c020d150617240c09060f0a080705030402100e060c0f010e0c0405191107021003090b070f09060c11060424091a0d 64
    0x5180072401c1005004492605902a440e16145621102500c0c84104016a2544141098040802c00781c2c0e0310364070041d0141410091103440102110140a010350300c01d03e00d140034501130b65086503155000e001600c00e40c000342d030f0b0118285006042130f00761582d40d03c0a1001140000c42c604070341d60007240340102c031402691421100248220f40300c060103ea42a042c1e0030034602d440020341e030200400d058170300a1044902903600900283d00c0f040c0e0191068405514200d020360f04110f00700005064a00c003806aa6100301c400707400031a800c0d0302541100d1500e0301c000401d600c45d9140034203114800680c18944925146d50345004628503064086000c1c82c0d01920701e0180d00840f0784513003030300364591643c051500a0300c5420310030003607140d15500b00c030b0f0f607454040402c0204000031000c0c424507000e200c0d0038116922a8107100d900166220200f03031135801a9000e0b200c1d0409121b2032003443c0d05000b02e400440e44007450f200c030031039141941382c0c501080300c03071646003140000048508445400340c001c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 527764091 1250 527762841 527762861
    0x131a070c030308040b0f01050a0b07020102100f09022119031b0c06110604230106120503070c0b0f030c09010e0d0813050303030103320607020601032022 67
    0xa40c991995403401c02800e00881103908455144440000a48402100030722505985000c2c000300301407400c0c034001c50041d40c0010320a0b410b601c6064400342c0001041c0c00740400d4050b62481c00700d4414210b20504c00114008001d0340800d252846007540c0c240c80020707100c1c0e036071410400000240e41e21420140d441c5800143c0038190b00c0700659940c020b000c5d01036030001c00c13619075030740342c55501080e0b505075a119041500c004040480000403c100d049420340160407031240000000f42c0c00d07a81d0090b42190458a80d411600364001080400910010203003842c010004a50194540300b03800804007030902c0000c01809020001081801c1e031070b4441d04011220501c017800051240da56403c003c64180c00c1003030758284400008601050030304010054a04899024201d8142c2c04141c00e07609607900075070f08084505a02609280c8440300c010411140a610313260094012541035003071125001a8407680c001c501c05290441090f69240d00c1640343c21740200303e5690a010180310a43c00103881081c2d0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 527765341 1250 527764091 527764103
    0x30f0c050607031a120a06021b1c170702071203110105070305010801110a090e0603031603121808071b050d110310090215030405120304030e010e0105131a07 69
    0x70040403a815070310a000303840340082d0102407112168100000800e48104015050701b11105240001e02e05030040d154000c81c0c1e920108050f00c0c4c814035285007040318407000c1503440d00800040402900410350039800d0502154114480c5088000030f9a102110711440404000320300d02c071003d0600c03075100c041203080ba4000a20003410b04400c010080c0500303010b07079169540780040c1c41c90150340e15011a0b00c070801da5203031017074007900e050a501c65001c00280301a80600080010448500540da503034040d1600ca62128504c4640394501c8034126001c01c000549620003e5500b1404900c511080e10f41007940400b1a46580700682e150114102e0f86a201a412050104c84142000310313015402c0080c0c0f10503001c5031954680346458000392082c52101030341105060034004044140c0c54011a0701c503000340100d030460600030441569541c422030b8150001003040d21004425a03000301c41404860303003440c041d4240107800000b8104000c80d403041c1503c1050064141c0d912519440680d01d0b6241c03c80c03 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 527766591 1250 527765341 527765353
    0xc101d03031321020c15190c1e080d0e03040e0a020c010e010c020a03080f01052101060e0406061d09191e0309030c0e0c0d231503100b0904030f0c05 65
    0x1001030755500500c04614822404046c40c030350b21400f40c40c15503800007054200d01e40c01c1d010318101038502d030300d54000c00d50f044143c4180d000350002d103254840780081d10401e0281d907110340c050f07034007000c0752045403a404940c4c0042004010400c1601c2046403c4001c00030700683d180203444050380108a41500d0200a50801680c60640e0360046a02240305009845004071075580c5094034104a00901940b68000e01c0520501d40c5075100310128a01640d202000242098840c1d1100f001c081017100e003110045c2e2139500500010b02d024044030700c0400000c40802d8181401c0d484070343c40da1a880d02d4000b4241078091054280141c0e00032803d011a55100152154000750500a2640107a0700040d50216203494001400c0100300441034072501d04c8100403805e180908000394042e0020401c10f04000d106001d59020200d800c0c140140030341c19034855258590820400d00d410b14007943d00020b43c2070b1421050a140b520780050300381d8044c0d450724200c404107044d0002500c0c0300001030b402801030300c540 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 527767841 1250 527766591 527766653
    0xc0305180a080309010e01110d08070c050601090615020619020f1c050a05010f080c040906020c2d0304030b0115031404051b0a082a060c101d030313 65
    0x200c014001c0c3c500c01c2c5d03030300c02d030150914005580308000f580238046a0750048141d11009481042c1c400c0d0407070729901e4848106c0c425511424584082070b0009031000c0c0c2e0f10042000100d9441c10340c40d104050500241030f0070710b0a040f14016440045401d5000250002250070521218108603540c16040160207807008a08540c694010401101c040b580c4c6c51401d0b0012500c4120701c14010100d03414000100840d010326010300020b4102c0320011504e4070b401b03116450a461003444441c17010060103059104080b4845007001c200725040350180c44c0b0750002c02c010300100c0c03c0444068151002c06041c0843c5c13102111049009000804101031440d01d40802d00007000404102543c120210103c19030030780c0c12400811582c0303001440346000c90b5008982c41542030540e510220503410f544061808982524008544190700040100b034490308804001041e285031482840414080e03480011034000c80c4445441e81c910020b41a0380d100680e4034422000c006603103110020203011081c44180d85030074 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 527769091 1250 527767841 527767843
    0x160216030b0118020f07030c020103060905160f0503010b0702330717090f0d02010e120114101224110403020f0102010c050307030b0d021228030c0305180a08 69
    0x1c203024030764442003011000c49000c280303402522003100455100304d24269032a079041e1501030200740102d0606849070380000b03418500d803080c140b04070302c6101001d442c51123103100107150f03a8000d071300c44d014004107000510544c0382140c281c0e44c0d000d81c10f880869600145100855040c0b03d03603a1071050b44082c15107229500101345016107030141c03141c7d8a2440c22455110103000038043ca900d030680008490b42d07120070601d031a4944070191801810041104c0310321802081010302d02400b1004036a44504580844140c90500a40d10a090703541c0242564280783c44500001d00c1c50030041d050b201124000794400e149006800a88000071f40b08004000f80140301c180103811920040e071107080c0d0141501515401800b4407150070000355607280c03455440d0f83c0c0079402011510f00481d00100c0c0c0d14500b00060300c0341d180407442600d1810040c60700c08805480845411440e005c43c07542443c80800d5840000c1c2c00c004e64000303403030380350800e1522546a00d0f0103070700e0000d1b68940240c0c0445025000115550 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 527770341 1250 527769091 527769113
    0xa09051c05390c130f0f0507020c030c030f0d0302071b0f18050f0103080d0b03100608010c0f0903030f050702061303050c060c0309060705030909010305161d16021603 73
    0x4030078440c0341c08000300310b8080343c0351002810b03035642251140a60311003280e01d40e41310031146003400c04002400394500440c0812618221801c0c2c0241e480003419540746e18007000120710b038800072001040d0558a054202c3e89402016004406054011032950100300190b880c5e110310040e4640f10313040c8955144615282c0384442c1c41000511400700750035000b0381c50301e0b008061007401e1801014001c8c0e440c56070388210030f03400001c0d421000c0b50b03102c0f10780d0041c1c0e6040c0302071142c1d08010345000c00c0740c40c1403100441c2101c04805000081c03090710424000c525400034018000c480e01400c14000b16160b030641919688900e8800a501c14000100c00350210201d074824010303030303006008076420010300318148080c0d44a01c820b81c4809901c2800721852a140c070034000c05003203105c0c8050b0b0b82040555001700380e0f1503000381c10031511600001c03034064480710014100e0307000303200c00910070b03407403400303d1542040650000d042400c0e82a24010f5080800d4000c01c100301c0484141c042c4c5030417031a070700d042940d4100c0c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 527771591 1250 527770341 527770417
    0x705061b120a180803031b04050d0c050301050c040315020307020a0b0c07050c0a050109050f0303040e0c030f0a0b0d0209041407060f030e160501080703090f03030506090a09051c05 79
    0x481040b002404048a00340e030b6029504008015031650f00c54000709104c1c40841c8110240b8100d0811010030a2b440b1030040c01a4607100389102c80d00541004105802d6031001005940584020310080020805a20001d10305480722a070059990b180d154003241840c40c1900302034100784110041c4112644c80720b00800c95207014800f40c601c2030003503104000103040341d48141e0340041c4030841c0600175407904441e0196102d40040850b442c01c0d5542c45c5070103100c1e108441d4001c5490011042010200c49400c801e540301080810402c000a80107000a1041d1400803010380160031441c00a4200300c1c0c07065443c4441800d000480340302986d551401001c034000d10075814002070400c11070008402001a44540c3c460200641049145c14a001103c90302401410501019201d4026a0104514101d440c1c44a0f019903404212031070400184190b81c00c4c06805200b0003441c2545c06000b26101180741041c00b40301c405000c1c10400003d10842d181e0180130034a06a04c01070b690301000c801c044d4900f001090b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 527772841 1250 527771591 527771597
    0x1d1605130b161505190e010e070303020c130903051602040e01110301060216031211030f1903050112050a330518060c0904020d061205060f0a020703020705061b120a 72
    0xf25002c2211800b41c44080c0c84000815103213100c41d0051181d9034000034103180031b1070b00006406444c5004140b501c10b00d54000d602507000f00b0200c10b038600304598010900e80c1100c80c18060341415690040071440703801e031316180061017600c8401c1190b8894200048088204e0002d12041c40301c0b45040949a000703100c3d6001620032503003644400760f0800403000c112900702d600010f80c01c24541e402e4445003d804030b2a09280030800054003048406030290120030400202010040000c610140c1200d406811021400a001c0400400200c0020703510416603403007001c0074a0102070078040b46042d100c0c0d465013199500a1010035038901907a5000a2040189100c50100018000000703038072041e081d20720340e090080c108000f444606241d001400080d58a000001b8410f594115996504440071030407a00740c0c001702c050281c0d03142c03580c1c4800d820040701c9100b1860020f031590043d558441501c2014001e0340d010510078503803060b44512540500390340007902d09001c1580c18183d441d1b8029440c00c808 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 527774091 1250 527772841 527772863
    0xb0a0e030f01091a130c0905040c050a152a1b0e130b06060918060111011a01030902130501060207150207030b06010c0c08010e071d1605130b16 63
    0x40d0841c140601040107030040d0b0140b121080918211000700c80003408088140800042d180c001036032005810000d06500300c00003a281080c0c68030341201d0b00c0300e0344484c1c856100d0303070300a100b500441042240b003071616050190101c80b0b150461a131003403141c0040d9843c4d140c1208508d003030020b94407180ca22450b0800c05003c0c15626aa031070004407100b55000e282c10303001b245002e000500c400304010b8100000400c0f20f0705008500d4005120850403010301840ea4100f05e00340042035070024005c1494040c020002e212143d40d80c1c488031540c0c45906c16080c10140ca5071820025901c072501d1003608000070240078080e0303603140c07030010759500110700c5070030b0340c0d8800e043c0031103201480441e844003902d07880300c0d0000700350702c5003001100c19000000d000c0e40c90100c1e241c000590861700340304c0c5041c03a9401901400b1b105240c10b07201003600e000340000000340c015450410048403800c251410554841d8104103403610200107142c0400d4125070420850020002001d0072009921100b8507007185c407031104022 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 527775341 1250 527774091 527774113
    0x70f12140a1a070e0d1a060f0105031f030606090209010206070504030203030306040e010e0105071d030105010308030703050403050f03040f0618020a1502190c2d1206060b0a0e03 78
    0x9555540050050a14a45030880b07440b00b004560350107400c01e805103030064100a07114001001c010880701e0490b01c091942003000510607080d1070b40d0350302440403100b0001030400400060528031004168a003c146400e04419a010100d800d000c06160402810800c00b40c559504000035400b241c04c1e9401743c0301e504000385600744580c0403035044d03a40c094003560450b15405c1c10b0002401100382940103039500d5056100d03030f0300c50910031148203164542da9030b65190125030b0700c0300040315000d003810b000f40d05000051010646d0003049a402901c107140c0002e403541daa003021030f0640142007055903404000400d200c02e1000080c50214514000d5404004005440386100301c44a0f906100941000654200700020303c1c81800418800429005454001006203880194902a010700f210b0032a14820103004440030032411114003140d5641403030500c2c0300300c550700008036164850030003001c1c0b04002d60400c206142c1c201900908000c808151580c1c40d251002d0442616031030054028821140c80d01 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 527776591 1250 527775341 527775343
    0xe0a080301060329040c030207240c020f06180a0503030115031a1e0109050406030605090606060a1b02030304170d110303100605030a021201060f0215010302060406050c070f1214 78
    0x12080115140d11302d207004c01c040c41032001900c1c5030104c90051544c248440ca0100b220803038440005204440810040c11490a00388111009804513108640c01b2009041d5000400148a070304a8501440d8444481140910751b19000c00302c04010610300010000080349283c40e50070b4584030610780ca05010061084202c4d20400c0981c032203607130b031040c10019407080203c0c0805c22219240c2e410f14048011319221008541a03c1c040c2d0b00031107149913507000700241f0a100380100380e0048011101a07103459202c14001740024088080603500140b81d0400c0300440d40c00300100d6009004403081d0540401c10401040d444110500310b030804500407038910042010040100c0c0d218003a0640924603403400c01c0c0048446410060101201c3c1e43e00300421088a600107008074000e046959928084140d01d4100a0030302d050008403100f41e074004d00043c00143d5412050340d0540e940c40ca04207440d210410522450010b10364060856041078260214018030106035140f400c60044481c5c0413600b40c400c8120f = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 527777841 1250 527776591 527776631
    0x50d03080f13170307032d0501050a0305070302090a0212070903150c05031b0d0203010f06091502030f09060d05010e07090e0f010b070c03082d07020f130e0a0803010603 74
    0x40418460741e00d0b40603c0d100200103581c00607840d190006030841d5203413440524844407140c420700b0802850320416140464003a0030701400c804d90300e14040320305c2c5039941036462455000083c07285902d4030000d80c80ae071855060701d400540100b1820071a00303281d0809401030000c1c1c0015034000404403652804440380d801a10500320072503465a20755580c140234801c035094002c404903601c80d402c00042218040b64009140a82501c0c0c5040c1480d504e0480c0107070000980303078441c030f0342d112642207514145034020094841c0302c040c0c000c8071035035501e14000180c26849242d0503411214681400402d0300b1350582d9030248501c03074544413144000c2d02c441414126035011900e0240395034072040103004028440300904000c40c854013500078055100d40e82c2140c260804240070304d03501050251903110300d248201e0415400c4910318070758948011600030400c40c0304003007080f50080c061503980c074a0070070055001903130b039400441c10ba0b0311083c1c0e1072510841943c17080c4030340030010b81000c0340d190643e0640c3c209 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 527779091 1250 527777841 527777843
    0x2b06091703100302010e120a05070509180604110a030204051005010f0c022407080d0207170405012f07080f07170a12180602030705071a0702040e010204050d03080f13 73
    0xb4125024515401104c1041440150f950444140081c0c802036076003c20491452034411070140a1803401c100c14059950380041090b00240d8440c05ca4071601030700401d5503600305400041080c95080b441d004101401c49a510080d0054540010001c8c2d01c1c40074030160342600c100342d856010082c9a00c0040701c0c800d00c0040041d6001d0000140100364140c0440b00711401d07040e402d030300c44c1848081d031a03404180e00941d01807140d071030300007858008214600c40b11544e0181a95080781c00c0904000c002800942c507030340700038900e2240e6140180010140c1700c0c030b5506042110111031585032103003910740e12007110000c1d030031040c0301e54800490302841d640504602920f0640041210080360b1320381c3d1802e482800074100030700590031508203422802e4044032010301410b070015980d40f07100c3c3c54100d14004007a40b080d00d440d141200c4d100401c3e80c1c00400c480c0703004c3d0102d4000c1404003c9030300c03260091140c1d40c8290750004840b480d410401d034011030300921500742d40381000f980e035a5541e12441d41c0e00107460 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 527780341 1250 527779091 527779111
    0x70305010f05010c02030a05011803020c0901030c0605070c0302060f040e06030d0c15060f0e01080609061b090a050301020a03061502010e0c090901141f05031b2b06091703 75
    0x14003400a07510504e010261140000c048800c14070240d200e0f24210b45020f100d07091150240c20148003415010061844080340c03d549210700742d0f1468480c0510700c02c01d8040e4408000b80014003405012180501c1030107107800510940d92003071148200003070b070360113031164005502001000030307070900d000b08803113001d10390070b8031110b49014aa6407020400710380001840440d60f0303189404030b8031240a00c0c0e8400641550740d030110080d4100700950f45000402010050030354801c10400031101203e04a000650b035942d110341e601d81619400082c0d4007240364021640541c8003003090356a0a50640007041140c0c0d0300c0e00d0035550141e00d480103c0c01d0b2034540b090040d4692002c24200c006003460240540e00100c200000189545601c40c0240400001d13902200e05109041051145000c20784403030004200c1280200644901119041000030950501901c80c0d05500500003601d9078911045405041e0122116103456aa150103001410f81101c140c54103508030814480c0d0b4070500c0116401565840 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 527781591 1250 527780341 527780369
    0xc020304090b040b0f21030301032607020a0e0601031e050a060602030a08040f140f0d0306062f120703180906050f100203040b0c03041a09060f09030717060a0507030501 74
    0x1406005006041030a001b0541c04c5080b01a1003500003800554042c5104042021101a50600a405e02401d0185045c02e1800400c550310050341c44100c01d0382100da07a08a00d101e1a03a40c00010f070300401c008500410f41c252010204203010604e41c0c030038be10600c50144200800394454600301d03901e001d8040102c0100b16001c002c2408910314000c01e0026030711078081071011b0320417500010704102d4881040049580031480c6400410307054040e08003d40681c0c07a100709550174081009544801c07020780001d03124440b480101d914482031003000500524056241d0359020141f030010a641030944820089070181c881c00f240c028171501808040344c40003807030701000c0e0308803404000b103160000d0322038001e6101c20440000d00e81449000760103a200810040d40c0c580e0b1506c645550602091690001101d5082054520380d0740c07800c0a45031304007041c802c070f140c5444080c40400e02e01043d079085400040588900c2e030b4488600007814070f12034612058203025907110848140c05949083c06035005441c121 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 527782841 1250 527781591 527781619
    0x904150519260a0c06030902092203080405240f071404050418021005180405010803030f09070506120a0b010e151303080301030602071e0507030209040809040c020304090b040b 77
    0x140112080710003900140ca032600c0340e99132240302911381580310030040f94a41801409500c0d1034820140e0108601a0f003064000140400090415801000400344000b2201090600c0340c10031030050080b0b5a90207010852280170148540032038101c56510750041090300003a4800e208081503480d464454000c5420107003000d00300006048011012060800d85100040240c0e07102c008000e00681c850301d43e9681e8603507042044290341c0744131040078055400c25004001c1e80c60008103c0c0d5000c07441106800540d12076a610764100100c9038055540500c0105641c6160300e29101080e0203211036142c104038400004005540e65000c0d4202d4591008141c4403a0940d5003440d002072940030b4600d4141e00b952902ca0340c495201c1d41080c0c0064900179030118840c010007052400c0410580e00c10300d100c041003080741c0d0750a42c0d54981404002d01401f43e440208081203050426111100e02c02030040c049044000c0c00250750790443d01c180f144860a0642c00030850074207100340c001d02030000d80030002c02550 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 527784091 1250 527782841 527782889
    0x70201060e0412021501090608010e010e070302040e101a04060501030b090f070e031603020103150f0b071e2f01051909030c0617011a0a030905030904150519 69
    0x21401c00341c000d43c005d1a06510070310f2800c405243c060007201c07100140352414080702c0c50031101007002d040100c1c1e1501c1d5a48aa0000c009000c1049981c1203174046170712242104468200654942035082950403c40f51101e502550306c0c1c00c580f829070a8070104a0b050350b50004405032500e14410035008000007020882030400b0015882d4000c4d464240340c1c0c031075402e40d80482e1415200094580082682c440c0078011589c0c1030040d503100000000078480c000f810312203404681402031040100c84107000031010200500052178030315090001c411180b275036603d820144484050310f0081c0e840800300d08540d902c890225a01700c0c10365036040c0d640c14107041031040520407802110744030100340300b0142000800903444031034400243c0342d20b956a0300081910004000b680d1410b0f00640c08801001c1001c10241d500c800680d082074245103804104030781107041041c194814000203907041400d0501009144440401d46021510280c454800c0020703484841913000f01c8500414501260310b13898030088241c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 527785341 1250 527784091 527784113
    0x10e060108061f0c170906030a022203141005090d081017030c01050705030c07062f09010e06210702032a010f0627020715050609070201060e04 63
    0x1d0050301c03003d1581c1100e6a04078000c007025401c2400144608003200c100880406607a60090048014504010a80002545c1da00005004801d0550b02280d19801c2d1000c80551301030b0541508100010360744c0b2070034055003074606030302d09800901c514940e2408121182c8603803071260300450b0103024200c0503440e0450380d04001810b080e450070a00e0f400071507900410300503c078800030f2070300085503551020b12200d402d481000344181c0921005000700404007a06100300c400c00fa5005c00c00049100c3e1700d81c0b840f0154103550307000a20180c040340303050149040c50030042c8220007007629804429003106041203050311640810348241200c284111100c4000044040c1e04014680150785c03c0180c0000401400c40311600d248048480340c1e414142845400e04c07030303122a03440042051145904145416028100d101000c20102d8100749200c42100032540c140d0741042e510140c0b0150380b00458545002400080d11818450344100b00440d40c0d0f030340141315060407501e042141400560f5141c0310008070034 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 527786591 1250 527785341 527785351
    0x50a0e060f0c0a031d0f0405072007090e0106140f0111010e030a030c020d0f0f0221070b060603010f030b06040b060d060e0718170102221409010e060108 67
    0x480c00748400380c0840c0d01800504180000c2000a002aa070b103810014105111111500303076004114800c034900d0f0716801c0e20480b1505040c0c4000c1441c0e1505801100c4801d0088050016a840710b20419074445c00440d01d0422a40070b69014044d003c8100b9030107080710340354030503400c5c0000f01c2c8030000018180307490070503990441414201020f8008008481c25a15800900d002941001655952032a01031088405149180c40140011080c5100c060701c000c01c6007280c2d105000806201c5801c1500c204800507512a800650b6048000b0840d01c01d10680c1000741c2c11a000c4c4500c0e00016902c0c02c044c41964100c42803141000d04007841d644030507402c0e11028152030780064417119614100d84800c0f00509000d1404440061110710f0701050310841c2c0c001600e41030411007800303952003e840007110720b18240c41141d500740448a011f966424024850502c81c601e580000303500813800e00090f2101c042c100d03080c00b040c4030380594007001004242802406400da0b590401c201240070355201d1080301e40d000c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 527787841 1250 527786591 527786599
    0x100f18170405090f0a050a09020105070f0215040803070605010806070903031404030611120105031b0910050405240307062a021309031403060901050d240b01180303050a0e 75
    0x400d4840010582c501e0003144c10494000000b4240000c50219115481d404849008100044600d030b41c00240303a84a0741c0c40140c080c010f0741e4508030940d995082d250304a00d811061590340c0e20b0f917624441e902d82c0c12045090764000c2c075001c000a41c49501117415031250206031784a0030901d0859400f81e52104060f81a92003c903c10321000c400581e0714441c0c01140004201d259490b18261182c1700b42c2804147c0240d0b000350400707120303aa03072000b0500301903204120440d81d4000c0e42c0d1b1445003071419582c0507485594028204818010160741c101c1d114410904c0e119540e090b980314400915a98505610900740003071605004001507030769415036401046c2c5180382c00d0400c041c480d00040e07013201800302d00343d50190b9509070002c10076030014004400e1000c52500d860440c90f001d0000380c07103d81c0511aa0f8003400c04000301c5c800b0020101040c1e030200c00413600318800c01c80d00c02d55510040003209025404144012010450200005260011a0f0303040d50f90340d1030001c4880049544c000744411040d04 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 527789091 1250 527787841 527787847
    0x501110312010b0442020c1306031a0405030409050901020714070f0608040218092a090c13090c0302040e010306050411180c130801090302100f1817 65
    0x41c201c0480c002d041c904441600c4070700704070302541c50007846251400040c000d640700180b606100c040305003a03946210400a01d40e88442810b03800d000d550714003c0d620940c1404041c60b4001554441c80680340140b0300d20b4454800e41d80204e00c0c01409440141240d80144000c20240761580c10960707001014100250401c442942c80321081f05c90810005c0d07450308013080520007c1191882c0c04001d00403403416100c6828150049900c6500180a01900350f6410001440411301048010340c141000016044c80b81d068028045042586c00c480714401c26210300815451414041070340d004034202400001002d00c0c05210400402c040e40100d8140750b000c5c03000250707102105c80c09074000c43c00340300301280e030340361518210180c00020b61a19206072100076140d06144406064994031403214000c6598400b103d0100c0815100d42c1e6000d42c8240d82445403400805a0204106401c0c1640328014850701c680f0000d080e05481e1510114030114008084420104a21200e21000d07010030001c0e082c5 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 527790341 1250 527789091 527789107
    0x708030a060308030412141e070614090a020906010c03022a040603050f0105090102070b0c09010c06090302010e010f061a0f040915080f0a02010801050603040c0b0d0e010e0d0905011103 81
    0xf15081100e040d60420090403001c0240b41d00721382c1d0702040c0685401035514101c0060f0300700c2d08100c4001800c40c00c40e14041a88010420f96a100000ba6032444511030090702d042c142c2030f135036080e05900c201c8c050702481c07020660ba94010310f035036130800c0d074150040d24092035072035458154100c80c4d0324180b0415442e5180c1c04d0094076180f14038000340d4003c00c0542200301310341d00c070745081d41d402034100400c0c1d81c81004001d010a00b0751101540004007400c00c070742c3c1e4520140040300c0d4a12001c1010307000320715100800041540562101d11404207100003803008064000c02901282c4051060760b00e01d821900c140040d00c80d556000740074200c003041d003040c10651209246012078003020440140140300f41c03028409900300300030712000080c4540042040a010303a000130000007040c03061602405020010030100b00206800c1c401500e0f40b0714215883e9025042d420016000d0000c2e07050303040d460007800c0d81440001240d20010405280c031030000c0146803100454000ca0781900a410358081444090 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 527791591 1250 527790341 527790353
    0xf200d1103070e09090705090c030702160f150306050f0d02040213060c1704180c0509031b010905030705030307110607052508030a0c032006010f030b010611030708030a0603 76
    0x60046482d03645001c1c682ca945014407190b220041c10000030399000c802e081103ea90b0f8410041e501000714581ca131349035180e9010685c6480444d119082c2b20180c0507001181e800355101400d0125000c55410307120503440c0002c00d0b412a0014020300c1d070441501040a010b500b0007610382c5103110b2000d4001407070030451904502c07900b00c05400040001d1804200481400042c014031022121303d007100902d0a443c044910451600c480e038501d40341d03070300c40000021090098050340c0145401809a90111485c0c40d08180303040340c1c000303030030b07002c1519100082803d040c0060602c0981314050001d40c43c050700c80c5c903900400c0f0465a81a80d01c0282086a9400114103100107600301401039031240300d0f24448035911b41040004c1c0c2107940d060f8414011403001e140d00400c900baa890300340c1055503c0340c41007a8034180d4034101c060b940182c0d11641d00009885091008004101e9004038604a9166206e1100b00c07449200310240c048258400e0041c0f2020441040040d50400d581d201d000504036901c0e40d5803 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 527792841 1250 527791591 527791597
    0x3051c030203070e220e010b031e060105040b12030304120221030406050406060b0a090e06010804052d1204080111030108070b030603070e0a050f0f1306090c0f0807090f200d11 77
    0x10781b000f030351152074031030103070604001c2070246600a075100400b41e1810300c01c25580e8141403003400c0c40b6076241c9241056586401c821010402d00b098203407030340e83c5414200084a03407007140c55900140f059113030b44a0368244071030044101140483c1c445246480706d0710b51101414001d0300917248555144c80004141040d10b006119414075521407103601880d000341080c103100c00138078050520080c035003080001400400c090b0341000705a00014070401c1c510130007040c15019902032500c213100b40c9060200d014072950203042101c424400030b005540310428020303071500084c0710309481c82e440f40398140100e042c140701450744038201034121030910b690745440355007036441aa03a411b43c4d59543c00c14040c1c0c0c80c83c0880d4059101d2034240c020405818a645200f56140038224050f0806507940c08440400c00303040f031060010200c1c1502c9400d05500d03a1215600d4524500c40c0128003440c040003030500f200035004511a494021100c00500c002a034110413143d0701603015403401c0c40e0303181d10304404000b0043c09 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 527794091 1250 527792841 527792861
    0x903070b0f041d0108060a090b0606280e031905030a050307030209040603060222141318050705010824010f03090f061508030c0a060b01090f03051c030203070e22 71
    0x3c0d107903d524090465003400000380c20381d03005500301321509000c6a007000440341c00c07100c00c2d11039960322030020070001d4036444010700490981404503118580d081c1c0c4000c401c10342d60b4040702a50024500602c0c071482114942400410035001803002d08d56040c0280007a5610000a0402501d4504444002000c454042e002100c16075400b06039403016401c4110408440494125041303110f90800c90070325000102404100e10801080900381d030a01c0340354002c05501804170f450b03035404041500e80aa1601e415009590004107030300000742d20150b0b80c075052003042c144c031240f0840a09660004480544122540000345500c07000310030002a9412590030001d0300075080050000300b6170400d0064a085940050a40c1e4802d203c00c02e2540d9022540c0308026038051000a08581c84800698407200150301c007842c01450300d0310000600c600030650200b0901e000904000ca40c843e14001d508900050b02e44400007101100c94200f1410194070031201c600151403040c54038803850921105540c0e035203503 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 527795341 1250 527794091 527794139
    0x1e140102041815050625080304030f080115080604020c030d051005010c030212070204060e010923090604020d05010b04180606062a1a09010c0e03030903070b0f04 71
    0x601000700e071080d04503120041d1142c850030310040b040e02c8550301c0e410000d80142446090001001110490fa6001d4040100d15289400c02c0c107681600300720485800440e000d80200340401a0ba000c26031160103094103a40140f0f24180400d10050300450300548014102d80c1c00944c200115101c0c03090070000340103452014074010030185410302c101e504854031a80141d046c0319480c4e404c3d50010b9000304982d62a1500307010440d407030704050300004018145a61045007040101400401c031000d440d0070111400050ba4a244540b940010b03680c40c54420071940740103e50402000328006103000d4492010441c010700011924800c200001030071104410341d0980301c2d080110840040200074020301009241c1424915480d41c041041515218485072010456013102c001e800c080064101d0200701003c15034101b030740180761041c1a68024000180300c00041021030a102001340340020807140c01c25005405000c0d0149055800004c0e03401010001c515000140804100340071440140440414100 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 527796591 1250 527795341 527795347
    0x1120e0a170309030f13091b03151401050d1b0e01080901050702120a020f03030a050405010b0d050d110c1021050601020a020d0201120501030b07090b0702030a1e140102 74
    0x407422910408094500307001009003071081012036580801a1016a010102c14503510482080c0500e213081280d00246031796440d0448044041c2c0308001500c2c0c01c0c440540b81041444200e011040360500380d40b0501c0c0d06520004550341c4035500c0f5002800320100b1025020030040c40c0181440700c4d480041500100040e80d50300c20503480c1d81c0c000310b16500012044001c000504200070001e4403480821030003048a480020701080c0d13148208440c540e69240e00095076100c1c280007034014050300003628182c0b859800d00803044030300d00e060f075020071495038040c0040c6040c0c41d80d11019078407101c1580c20b10a0342e0048a60210320354888004040e85036889a4400c0c2e076210f180414078100518074695500c41924040402c086641c0000c4e00400d019012201c02150341d0742e1f4030049410004852150011b10b0134071000100f00074103d00136a01814840d20383c00c0006489100302490343c0296480a58180d01011150300402c10180c104820001d40c05541602d2480a486200c8800105003400e10143c1d400 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 527797841 1250 527796591 527796593
    0x40f0c0e040c090e0412050c0d020a140c01020a061107050a12080907181e090302010606020105010b0a170c0f0c301c0608010f0204030c060c12030b01120e0a 69
    0x10b803060a50740301203810841c0711241000b400030911040100010180001c007a52001c0303542c007440a40310700b201203004035029003070b0300c0c10003c0d12400404011200c0091065940312240004540418001011780c01031007050380a8840387c002d018651030b00b580001080140d0008200c00b8408100d40e51700401c146944c4c000450310050003200020001d400a030413088003031000c98148480000d04c0c02141e0b00100c0d00881d000a04441100c4130022020010302d003901140425406422003001c540d000e4008005c50381c0d8840c0c81c1e00c454800c2c0307480b9200090200c040350460503061080d0b04d402a4440300c4c900d003040a0b45a0512069006c0502009103a11005010308500e5003001c03064001c962550218140c58242d071104041c0b80511002c40110040008036013110035182d40c01003008094a400038000c1c0200b001c0408000e51083c0025964401c00c101c1c00300d40140a803140400d4241d1002d421405c0c4580c603c000c9004140008001d030412015a8007101d0540c031501580b41c60740c0000d0042c10111500f = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 527799091 1250 527797841 527797849
    0x10e0a1a03040b0f190f0f0509060412080c09010c110406170105010f120b0405010915020a08060d020127032108070e0604091e050c030121050303070e040f0c0e 70
    0x824808a44c1a00010020506807000031454850050980868541c21500d0042d0140a0100004007000d141000300700501400081e464040d034051080c003844010391701001c40303040c00101c1b80074007200c008000030070309544038003c030035880c5010300c3c0e50380254050303200010f041c0c820540c4902c0350603402d9000c2010509003882068010314413085800450b516064000000540d5041c003e80b001040c000000c0030710a081d007202c4445540f002c0030030000501050070100030340140640c200041d2402c0c000440d2803c3c8407880e01034050b016103901c03c03a4440e0558244184c90115210b800b5400c00070310001c001420550014094055003d10f00c14141160100510403c4014981820440070901e200c07001c0c0c40e139004940c00e44440b45c4010070742c900715110413102007040700c0925900d60300c2c1400f0071a100c1001c0024506072140d1513540f81d2403a41c00d490700601191248805042c90300100082031005005101ca8009908041e2002c14145d003051000021140603200d1400881c0e0126115185071034 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 527800341 1250 527799091 527799113
    0x80102040528050f1c060f1505090408131a0703030f2a03021b030a1e0f03052e03121103030a050919060c0810080c010e0a1a0304 57
    0x1031000188400250090b6091006a48600c9414000d4040608021050700d81403100d4118600108807500458110b01c2e00000904280011050071843c0411041700c0c4142c00d1100070444400800b4045580c130b881d00c61604580c07007001c60b2020008200700001d5900800070601e91200c1c4101c2ca29034540b06a420042c0540c2ea580030240c0105162042c071010341868031004200700510030b0301c1d600761800c0790001a00244600340d058641d89400c4100c2e002d03034a000000904002000e981c52100c804001c10f8080d4072000217540d00001f15483c00442c001a038465071009500c00d84955000700045240f111041c001034010060000c0c4003000401401846031050285080001500e0f28809000a81400f5a00c2c0d002c040c0290b050540c490010039201d0004000c012543c0e8004041a1101d8549180500c014509000d108020a01500c0010004204408400c0403681d00c500035180046c40c1100454042d449116810740c03011407a00007141000300212841c0e4241c41e9001142c1d41d07030501f400d1200b4600b07 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 527801591 1250 527800341 527800369
    0x801051905031e01140946120503090a060c020c090703091101020303100308030a06050402041502011a0109051917010b0f0d02180c0d050f010509060a05150a020a0c0801020405 77
    0x481800074000b040500180781c110001c0741d0400410b8424142082e10b0082001f01c50308000300d1301c0e03410fa1549035081e0030404906140324103217402e4001700035182070b5400d0004450201c1e454200084440200e4820b800440380f4511031b2055800104501c00054184c0e20300790b13542d01c0043e075200d4180b010400e41d00340200300030ba024002141189412596268402140d00004140b03001c04004904a100c2e03a030440409014010415034549440c1c1001d82c0d00240080003010040d801d1000710a1506041c3c0d040130758034481030352134400307079400c0c10140043c2220000104245980d52000051103c42c3c040204482c41d441ea0004103904034642e0402c640c204410812134850010b01c900c041c01a902c0c030441403820403105103400710347c0d90307001e103810014009e0050f500030b180e0a0500304580a1802c40501d416030340c0442e4072800c5034807290203200016006001d55600b1140504171010030804020190602520510460350000700c565644080c2022580c8003868607900818140454944000300c84103003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 527802841 1250 527801591 527801621
    0x3030a030e1605280806090c010801060806061228020306100908100509191a150904080c0a02040f140112050303130f0803090d030f0207030801051905031e01 69
    0x1403401e000010b10040395135001950310403070300c4d44603c44c0842c0b00034007800205821360540740549011585192103da509848c580080c5200001062041c05050303010300418001c0d024905003079020741c2072205828081c0141010b0200801100801481d0202140400c040c1c14030160308d90030048280220484644001c105100e020441484100c40c0068084d818200c0780201042c19241d100840703050415030480d444032507018050807020302040440d1002c0004000054002980d20040e0342500c80c4201c900c1710b80c0c00201040402d01054410005e0001c45410206a0340c0a009681c0044c0c22181011180c5510079102c95a10242402c100700a0307005025a9648860b01c009541c0c1b00781e2a0301c401420303910b04141e249001e40602c43c1d039420021000c0e9100059540c2c07824004901a0354102c6803100600203410407101400308203150003034859590707241d1a96032060342440b04025843d108119880360006040f500000c5039136041010f1806903c041c2465170100d08080708103070a48000400c19207007 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 527804091 1250 527802841 527802883
    0xa030c17040e161e0201140a020a0e040c02031308010b040c0201020f04031b030c170717030909061201020310210b0f04050106090f2a08041401090203030a030e 70
    0x20011100340c01544100341d20070031843d842034090241c0d041103a00e00140c002e00602000c41c0d80c40d0703030150b1052082c017140003202c1c001381d542c01110394140d01c120003400c0000340f609440300c82c40e030820707800c14091500c8500640342020b803240110316883c2c405a11130802070b0f4683d0b11140140c02d140c402d5020620300c45c030083d89451680148107103103205034030004107510001c2c003040702e034003007100707030840146501c03000a01090741d45415075800e101200103c0203c1d40658600041c00c9541e000510030303004900c0340a103040c81c0c00d00c0c08009030322034000c20807034200ba242001c0800c4542e080c8002d6215290450320303c0c4c0c2050819004444004103c010580317665500896500415802541c00d03501c060300c041d880345070341d90b5450850702411356039000390750050401c1585405c0858a070862428100e03180200700105e040d211134454801b1011089801050b0494081000316030400000c0d440c2d11860030000c5170748046c0e54007191031a031220703440380d000039070b41c254440c400002405150044d9210020780c80c5 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 527805341 1250 527804091 527804099
    0xa060e01050f01182a0f080103260d0f09121704080c0118050706170c0f090a080313030b01140f04050a06080a080d0e070f23030a030c1704 61
    0x640c50b40600079103140c041c80d141d00c2c102c1c044250704040d92409800c3c85030694448a0f5a1400340041c66484c20000700c0c5c1d103c4520445140714030360641c100c1c0d410840c00303100c290f0b1b00b0540700b1502c80f5425072007081400c100601000d0b03070800e014516100340b0f840b5001039854142d08040080040c910307000000c204044025002d482c000030390ba40d80007a040380c0c20320b41d0b80ca5228022401880072401e41256007440916600510101060120445119458064642c3c440380b241154030182282e12403051072052043c070080341552005441c0c441d501815407808503444110f03452558007c045400501c00e80f40505104004140011a006000b281c240c0c581c0070b1f10300c42c005a0b200360100c6649008503605c0c000684a100c4540110b001006001c0545220081e2400e0455850b0321801a01a000342000d15035110b0148c00075452085540d40c1020440207070401b0103204403c900f4114001c2040741d107050500090350280800001c1d41d1081d160042101c6aa1802c3e01000059145518480c401480104 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 527806591 1250 527805341 527805361
    0x90f2a0303050a0806040902120601050a080309010203220305060c0a03110408100b060409020a0507021c021809120301060f1e02030a050f070503030c03040b0105040b060702060c01060e090a060e0105 87
    0x140000c012810401185e07510203001c02c4c014418600c010b50b1020b55140d00c00d038030905c003144090513250191174034030f40d00c1e071601540746c0d03a442201d212900580c42001405c3c5200314100105007030811a109040c0b010390f4a1701d40c6460800140d841d400d0040340003032240801d5405100340210581c000028600f02850848140c1e03e815034a5120301442c0c0d103a0b40c09000d0b680d41c0d1000ca030064404000119124041d002c4014115003181104a006411100601c5405c3c0001c0955000440c4c1c000c101040c102c4c41640c034480b04020186c403041d85031040703856042c004d0f0454806140030385150f54480c42e5039810280300501103030381310003002d41d03003c1915800e00d0704030303404012120b00c42814100b030b650f624180e8606022502c10400c000d1f1060101005000f03081e84040000d5004038000d0707100e8203071a41c0f030b003041004482d480c982c0103511031000c005203c01810954054001302107042c0002981503515002e40b90645412078661000b6080007104d00c0400585125406581b44600000c02191501301412 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 527807841 1250 527806591 527806597
    0x4050d0b1807053706090807050d0f0215070602071a1b030105010507020105040906080604030809010c0210230c030a0c031107020f03070b0409061401020c0906011101090f2a030305 79
    0xd6165400d01003400c6a080e06502c1c408041010780c136886904407030340d44074010414801c900544200e030140c007000158134500040209402c9820040c044243c82c0303540c4c20400490000740f40c0701316605040c8a484049121840640b5029010b900d00c0300b600341c80e10002c83c14450005284c0581054114410b880c0d80da0640e06a80c103443d803e0030107550303e002600040c0c502d40582e034060030101e41040b40105a80c90089078080c020740c03017611500c14a46890365080c1c00e84060030700c80c00050780581040842400a034000e140040703500e801050000501042c02c0c88030400480310b651003820000107016110a00388614210044649401c110700803e01e0301c0a80680301e0800f0107445940243c1c031080b166541444000c1c010013010301c1c680d5581d07680c0d0910a01800d018030541041c12500030540311954000b25907821b18110050003074115a03981001507034107460800711040d1942d0b983e01540c0010301d0382143d9180545c01003901000d081c81900c04103941c1c2401e0340143c0b040250144041000039084000e03 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 527809091 1250 527807841 527807869
    0x20403060c0801062d05070b0901020c0f0d170402010917010603110612060607051501060207090f020405030a060e01020c0d0806040605040b0312070302010b0a090e0f03040b1b0304050d0b180705 85
    0x1030303058030902602c04548600a007c0e010b0700e504421010700c080180c05600404002d208a01034a040055218200e510340700440d003280081000c4859020b1108201e80a0b640d11510506203854044e403035100408910f041895440d696a541d01d20500600c0761143e600c00c0002011109180f5024080246898561010b40203a0040c40d010a10000b000414031010480b40c8180c0e034400c91940e0340e544c00135aa02c8062182d0301c8924540f80c01d61909a56034002c96060340d10280c000c1c089603400b0742e0b8440080c81c032150004529582405006007404040c009008a11050b40e160240c50070800704100450741c0607400240303e903141c40d00500440d240400e040c2d01d10800e2411140c0c036500340d42816409050b050320174940c80400b0312400714012900790f020302c0e04600400200e61086c294055495903d00c290700500413805800c0c080d00c03600301c041c181070022045484040d40d017050f568501194480310840001c4910810140030411501c0c440504e070502d03080c181d4010203905d0301c0c00e80032888016a41c10 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 527810341 1250 527809091 527809157
    0x40b010f1503090501090b070c0c0905040c15090512010f06140904020d0501140c0a0f0305070212160f060902131a01030c030b031515030120031306020403060c080106 73
    0x401d0b101340b0400b0341c011480709411000250040c507140000401c9120b4400c82154241c40299001c95000010321a140c03085901c1003090309064100901071150300c1021041804006038103102095a0b280d1801c030440041c0410004168190590800c10070b40e0b44c2500f242c240795030410b03026401a582c01704180d42085d010f03518404008460700b8030350f000d00003020343e0480556104003801104440385000b0050102d00f030740d401005060301c2108600b0340b10306481d14001a8040b514484000c15840002d0001c07068040001029064076510011002034800c0700361080d0340d50b24208425810004a010142100d00804201ca03d21940010600d44000e5880724101956140f6a014141c020b0703100e000743c1000202112020001010003410b00d40c0115001c0d141d803000b208440b241c034101401140d2010302c0310070300f034084038002d810f01c806d494000038148011540c051346444007007401880240059801000d000c51060210364016120317440c181d01985c00c0000d400546400d07200700141000e58550203503 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 527811591 1250 527810341 527810351
    0x402072a08070803030105210a1101030905060c070314120f0406090203152a0304020d051c1119030c300908010506010905030a06050601030f06090203040b010f1503 72
    0x810410011150341d04040514070942030049400900000554100e980c221603000c03000f00a4102c000d20130510f070301c5c00d581c1540403c1c00e020000d42900380164102406250002c0c282e0903a8407518030b403407020394602d5031180300010b0001c24154400d54016025400d1042c0e24601365141d0745030101c2c114002c004d03043c0d00c4844800f00381040819044502e0058005040340c10307050741e1903560b40a0340401d41d18200300540b071018994403a802000c0c440c80070603807200c4d5039046980b16002d1014041c0d010340c0417602c0d4010008140a10f071410081412038642c1587c502c4000043d501c605440c08241b0384440965611500850b00002d501446e89051103034096400c4074030f440e00110200290025400d600d84040b81c0c11009101c02e40d00c084414100e9054030b00901c850345600c00151044001ca0261a070550800140790001ca0340d990000c903000201850002003100c41310518000b00c420710b4120701d0285d80c0000600040c448183c002c9400340a0030b0881303168451501c2d43d0600065072078000340b0305041d11a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 527812841 1250 527811591 527811653
    0x30e0714150a050d18141006050f030c041119080702150c040302040b0321090f0402070b0c072109030b1008070909020a050604030f23062e0b030603010605040207 71
    0x9903807107505c8141d200307a006070104640c050594071480c0c4c2d6a8861001031034200009111300e80051411095013019021b480711164200520003d0104011001c0082000300401c02560340f043d11206107100160b07035105602d0920880007410a030030b0402c010107407050a003d000380151150201d9086a40c1201d002032011861030100e81001c0c60300c54411000510100306030a02e600803030041111b80c44c201c40302e05030350326803030100400c900a16030041c0c900700101002600150600d4014100305001c0c00e94801407014014480141d00c464844000c0024050036041041005031041941c1002c00c004541140e83c1c00c001c1e41e241c0ea0a02485540419034580440c0410342d181c0711070b140c02500003d07101554a54690900e0210010243d201f00c8000e5090700c03515010761003060729104405039600c0a812641c135488012810b103038001c07425803003c0080840c1c400184500303110000040c0b02601c010340e00e80c0703005010075007101c1c5654401740c000d60040084400048082d0f5451504500c02020700741d0201d20 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 527814091 1250 527812841 527812871
    0x1020109140105100812071403040b03070e0a090e21041e050910120b07140a020a030305060d02010215101a0d060f0312030c030e0714150a050d 63
    0x40300e90050100c00321680c51096140041d00f14038031603001d046502c1c02c42aa1a81c58a41d5440e0610044d2022501440668000f800d1104400c00016614040341c0c2043d4440c1c001e00c2040e48184d84490214103030706000081030801d00110001415041c0040060031020200940c481901001080342d50701000b01d030002280c3c02006450103451221441400c0040c00c0c0180081c0c0c21007801010310a59821000030000c0400942e28020b884010070003440d0148540d456000a0030042c20410034050240c48458000c0352400240c06055415401082c91b444030b41009421501c02030682405810f1480c560005070360001035483d4402c1e447e4107444400e0340c440c0120000d500080d0406000c80d00060704c0c410940d6a81c0c8003500c0d001340c4010b4104075080c1d42d0b8007440e017492202e00c0001d2919002d80da400c070b100b81c0250f02c11220749605003404540081000300c554280700303403034004100b008a00707503c90440b820020341640505940c044a5490b22041050284c240d0040381c07103e4071010b444400d46032103141 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 527815341 1250 527814091 527814101
    0x3010e10121e060e070b090a0803190c061803030518071d060f0901270207020a1202150d06060305060d08030f1305060403030f0507020d050f07060b0d05010e060a0b0a14010201 77
    0x982c41d0646a4072038840c03810781d40c20350046c0e140718440d4071400004a270814010089402c28031303804003980303880e49000340155041b042d5490151116666950b11b0b401c010041c1e54440d021a00c00e590006d224a00790707140310040700841601c629140c4c000ca00500c83d1a4101c14070000003615104070100d190b4460000034580d0682c5c0322040c1d01b05030654000619007006402031000b802340c0042c2c580380340c149000240224000c0b01030280d84002a9801040b81c4842d629400d042c05001803c0d41d01c03812002c0704000c06076809651361448190f41c03404200000ea6040c46801d07004a012601c860022a180e100e0480324040940f0b0010000307000c0b00460543d038410108404e650f80c0c042d040c0c1d41c10303281504001d401800c010400b09001802c140000c1d1800c1c1c80494204c00784015600c0307050a0802000303001543d90051082107402c1591507094400540c0c4481d4070001c114411000031643c11128a012410300710050580c1c0d11a5003020540082644e41e42802e1041c0c036114910800d1442c2100c0c0101c0c0980 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 527816591 1250 527815341 527815361
    0xd060308040602151305060f07020c0d150606020102031005040b0a090c0903030305060907020d08060607051f0b09091209060d0504050106060f17191103010e10121e06 73
    0x3250018000840d0764010074041201150251880410f550b51000241c940d0303594540180250410310004101e02c0c0e0b41d10b01184c110801c0e00c11902d00d900b02002140105110341e10980d241c3c1c41c0c01500e51074681443c003500019103028070003135046040980d01d00d082a40b450240300d02c1207072202c1c03450a2544030340c40034600801d1000c0301401118561480508003000d14002074000a0070714000401c20304000c0750840c040c42a981c0205101d0001000444141101514081c0e00040800c070303241c08560100110766150488160343c050007030500100c203003210311007415640682207100070421800c03004a45103005020f8805801c1c0d03549844800140203114103000240305a00d040140014400705500c01420350f40ca035224009041800c030f00940c0c0303c00000402903030040000c0c0000701e00e0391424040e98030f140c1c80000e02042042e110151544c1c1500b00b40c02401091501004000ca1368100005003002001490b8403641100d81a0319400410262842403210100c440c3c29108100301903540003203412 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 527817841 1250 527816591 527816603
    0x3061b121a10030906050615030402010e01020106120803091009020109150c06020c06160315032d080a0f0903021f0908070b071103030a17130812090d11030405060d0603 74
    0x400d900c2c0241c000c0c9190201540c0441c5004000384903414000071400300088002c24a50666a95500440c1c102a800d45a9070455407195000900509840301040e542403090341110f4403460301c01c1c02e003031810385140504c521a60400040380007603600003c102c070907108140e100601340c0d41c01800580f900c2040b8280102117a20000314480000004a07140c1d000b042c0400411500b8010035900700e0694154844003940a03400000c100001000d03c04441084100728000410045003000c51100418031004103442c0070b64000f80c0015003036806001d0101d0142d8608010403001c1c107540100300000d5407060f2420001007c424003240e006d002d170340d070100245001c0c0210780305140c60301041526a0000f50080345c51412100c0c06030b515180220940308015015621548200c81c1403070b01d04c602c802e024208024240d1030700f1240c00800c00d9000107141101d5400440125410848950342c5803c56404c1c1d01c600704443c410303c440700050301004a40448104641c0682c9510340c24041400424103070b440200a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 527819091 1250 527817841 527817859
    0x17030405131a091902070f05120406020d020703050318060919140108040b06101701030b0403090902031005090a0605030a110405010e01080304050105070c05031603061b121a 76
    0x8461072034000c507542c00303400b400100e40c2c00c03110301c2800750a1205880d41c103100004200094140c0c505130f806010b20a015025070207070ba410b83d448071030800d00744001c4c400c0388940000c0c060009035010406841507480c0c1e403005101c842d103103488064880c080c1e485420f05640b11007180b1302141da00d800503209594002001d40c1c40029681d00805003110061240100b500308440400c022580201401480b81c1d400100d0038085681f4801000302d04480c1e01031000034000003070213802501c562502420b0207140304102209680c10300b0b00380a001400c4076408000031034010002c100d08100514255411201c003076402840c1d5032100311801c3e0285c07040e908115018030619102100784140e0b10030155504a0644d82001541d8a03680c2241851409008200142d0b0080104101651180d8010402c25028269100c98030f40c6400010382451488418a4240ca8440c40c0a10500130b961081018044820804070080000d00c070740a08041009810246550343d80c4007441d05889542c0c0b10414070702070081179044 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 527820341 1250 527819091 527819119
    0xa0b0408070c05181005030d17070306120803100e160c0201020f0322080109050303040f0204061d07020d020309030d0e04060305010509061f1802030a060302060408010e240117030405 80
    0x1c4040041718000b9805120302c40004041c2404074215120214540d2080315121210201400040c4003910403400c0681d0b0381c07070000302d400361011525141c1c2d20a9180c180d9a080c24018035400380296081408040b1002c810b102c080c20182d42d060190a1403030905c2c2c4083c8920380010303403c1020b0349054200300c2c040040c2d1a480725607510800004229039481d400d414603102d81c2c01c2c0e0308840140d01d00406551081002c20089443c4401943c01c5510040010030165154ac88a403040803002880041c03528a890500c04250b4040c004001e621081d44001c500f0312030402c00003541c820100320f40406000005512107172503111500031070042e58000c0c000744250306000c04003a40c2c4150071580500d0600910607070000044142001804690310210300c00c0c0c1e680303694050b0400035800503200c1e000c07035540c8940000040c0c4401c07001d4001040e030704000003081c604c40c48425040881480410f56640604801100074950000440341922108100607600040112800d440c610903500980e9000000900001c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 527821591 1250 527820341 527820379
    0x30b070309021908031e1303151d070501050d0e06090a1a091c03150e01050a0506040f17101e14090a08250803090c030a0b0408070c05 59
    0x14000d50b2081c2c0b803122030250400004100c90031640100d04c0d40350002c20401e8040e80f9402044a0860042c00103107181041130300d00b00d00d40f01083d900c201d480c0e10004456107441020352203000740351000c01e441ca207041000c03d4209501c0b02468020700e818058045441400550070b640710209110700b500c12100c8504181e03811594852121408407462905010207690004803204444c0c0a2500301e4010411168641e000d5031040c0c6d49110180101990740d44e14109981881100000402950070000391550400050204104043d00000d01603002000304202000c42202c80d6012a01d144600d600017001d0203503c0c90409000e40385800c1040d0800070365030100c10200414010300d80c49544100b00c4048032000d052540482125040d40755007099441c6030104100c03100411030b9000d031300c6e144105080d0045460490480b80141640c2c015408402c01c03004940802801c207050f01c08a0040c0038010095807050807009005200030150040455100100304a580c8404003a080040c1400701c04285c00d083d41d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 527822841 1250 527821591 527821601
    0x60d0b041811030f0a031d09041b08030a05030a0504020111030d061e061b17041e0f03050d03181e05010501090c0f1409150a09050414060f0a030b0703 66
    0x1500e18000342e2484000c5490002055101c0150702c00140c4010300f4039850075150280300c07040d400441c0b0402940066140c1d107a01086104601c05c1007104009580d100c00b56008600b0341d00010216401046a00f42154000058a6100343c444170007080954031740c40101d034180c03076989803903650b88000b103500328045859420036420380b1505002800d4544546640b0b0302115040d11941c804074031a1204c000441510003240c0c1c00b1a40204c000200204010941d8100c035803096220f0413601002c0b02c404d1a0711107582800b03400401740000807601050864036080c1d03c0c0c440ca901104241643e65480380c5504001c0303042600844d07000030425104010000c641440242c80c4d80040b1200d511708400030801d40524801d0103000d0304d2642d580305060650401c19a081580240340c0c2091030000e00c0b80300840e680d0b80030364981c2014000102900d6100003030000e009005140c104034859070400e1158690305100c14007403a0301102c06c540c201c0d00100e914002c82c0717503440d0700c3d00061b2000e0201d40800c01c1e03d40d003607008 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 527824091 1250 527822841 527822843
    0x3080304050d080112080a1701060903110909032b110304020f04050f060f040902090108031209010618020a050903101506030902030606042309060f0a02090f060d0b0418 74
    0x2500c50300e02540000f150502000d014032403501c0311180205d80410078840280c0481c4d030a9082401c00f20820381c410f075a00c0c4009074800c100140c8900300c140308001802c90807950704c41e015903444040c2d041c40b903c03d039124003a8031b144018070320400c0740030300350380c0321600c1d240c04010702c0900c082142c415040c0c3c2060b950303401120180e00075444002d5281c442d04161180b1486210014500c0000791528002c01160700e800340010b80c0d21036110315078000541d560352212030007448514021503650030740f40010280e91000814104459140840800102a036090000403841000c6001a0303643d16107141178540e030181d0a845030f0907100e076240c0c2d5605000558070089004019200143c0f0711541d551040b419a5003103800290981c000c0c8021901c541072a4000d200361000100e00c0f031041f0a071490750403215490455000d080d96001800344a503009084141c541c020305002c1e402d5203860715500c0840c200d60312141ca114016440082e03118030302c3c070b1598000ea1140310020014801c7d4250400c000c11900c0c500c50b0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 527825341 1250 527824091 527824093
    0x1b0c0305010f0c020d0c061d0624091501081e090607030b10020309060306120d03021903050c031b16030e0916170702010b06070813140a1e09060308030405 68
    0x5804845000003414005020186d68007040c0da211587c50001403c0000c40c9030300c462048003006164007030140700340c0d449940602c0144000721410607171030f0001e14101d1090b9000f0130080060101100c114689010600300c02c0c20a00d10640700e0342003201c0702c0520101c0310000a42120306202001e8030103c0c9182c001c6140d503409000f501621410044883d40c20a16500942d20400c000f0a136401c01501a640c401c80040040f0401c400142d14141030010100f100d80000c0d50005000c10300d0103400521401060340c61404000c0362030310700400c150603c4040c007581400c07030b0603c0e0400740f683d0180048514494054803440c10316015031030003420f00402407084620490b0500d0000d808142c00d0f504200101c0e80d42e642c1d03030511070195942c1c04103843c000b0f000041155200c0702e1001090700c4500050007031910a00c83c5aa44d25500501928140116003111401c0700c205002440e0541d2180f40c403400b9526025807510428540302c114142c0080c0a40c440d6881504143c1e0010901182101031171265010340 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 527826591 1250 527825341 527825351
    0xe13140c090a15091d0a24232707051e1f020c03011103252115030807050609030a09030b06010203090904230303161b0c0305010f 57
    0x108000039100a00300f2071580000342c003400c1101d440c071038025030140044c4140c041c0503000400305071360425000d0141540c0b1000708140e80b00e4122032900c01e03c9022913030070400f004001c511841d040280d896150404080314868408103810010355147c3c001c5800869030341220000700c203e030561300c52445121b25403081a880000c00b1942c0f03104600003208540050001c0311103000301c640d80c00f9a0006224000c11807181450b00c40407514240f00e403500348400c0a144c1503c92600400701a000f01c4001441800748108a11111559070448040442e120035940c040b000481076495010040c80d401000303104210403c038000060050b00d40c0140803150007001907442c4c40d41c800f0072850fa40c0c031800b5045d0000441c103110070004a07491814403900001c0500c103503880c100a210008400c03540c2a18161124501220b4107208843d136202e00207450790000c00614190300e00290107071480c3c01d55480d03807010302c00802c1940480041901410040c140c1c1312807001035054480c14118003c0140c4c181502e640d520301 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 527827841 1250 527826591 527826601
    0xc0105040c1d0609130c0905070309060b040b030601140d0c030b0907080a08040b0a0306120c0906050a0605031603060806040b070306050925120608030c06150603010e13140c09 77
    0x1400c0c10900c0f8110161045025458a00800b5003407a80c0354025107031190000804a50302001e0b00030b0307500031145540c003c100e00d421820304100b101d502d00d9510b4411480c107440418140c40c00304034141110281d00781d03410100e1039400480c84105070810004c10208551001004121800a00600410200e03088586141d02c62920680d00c122146010382600014841007005400342401400140f046140109030785e591441c0c101c1c01c08218440c216400d945d0714005000e6940b9030710551700105811501d142200b40307450b002405c0c911028024409124484900301d101ca0300030b0f00400010b00c03080c4100c840c5445c203400d00c50030f20202580d0303541c0080d05100b00001e10346840386086001d0580740400c00240507034500101e01c4000e6031001c0340180840315050f0140307040c0c03038800d42c00100240c9024540d11283c46807221705220008003644c440070700300070706416282c81d9031040d40c0c1900c52084540c000e6444030650349900320756414005116504075004090710013004106285441401d0721548066110 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 527829091 1250 527827841 527827889
    0xc01060e18190609030315030503072a122a140108040b0a05040501060f0f03061b0915180902180306040308130305070b041109010605041d06060c0105040c 68
    0x2d100c0b8004541e0a480c51090110b070550b4028200c440c40390400003455058061304036166074450f80103072166017020480c907080c094840303c40403c0e650300499004601a409482ca0021401c074010703403081d40c459030095410000b224106400d150104295142038180020100b24800f049000b01ca1a43c2615841509a54068502d441c0901d501c04003c80107585e0301c0a5210040070f009105950564882d100011315040d620b1030310780545500e0040d0b004450540c1000c0d000d40d44c007103036585001c400b940c82e40200c06520400701010789070340030400300ca05840781c83c0c104c440c1c05c40d41102416541c0f0441000036400107650041a016503480c0b1282c03d4480d218080544407031003103078058007142e003e600055004000e00f04c4141958464100035003088807544031301800d000300300d0f4101c5140003501c00c0011742d45000700402e0700510007450640d180c00e040c408400c80004c00710250384500b980300404a50b00759920001e0b52180801b50008212a14290800e4002c101240c8a18085080c903143c125010b070031 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 527830341 1250 527829091 527829103
    0xf02030705060f011a0f0307081e090303090d090e0703050c0c0d020109030306050f150c0111030f0603070806130308070302041503050619030206040536011a030f16050c01060e18 78
    0x1480d10055400c588d101c0b1010b440040008205440c5030442d6058040c44100750041d4500880286c00116141d25210706038515140300081401c0602c04000c03000c0058003031510100b41e03c502c60340b40c0460302d5201d101c4500090b00807003252a0030b43c0540009000000e0341540100c0e010341c02543c0038020a80c0e14070074054480e000008490300550103808058059103400010928008420000101000e00c0d10144880340c006a46007000c02ca038003814030100303203010051303180905144009403805046c0b0700080c1a01d03600340c8100505003c0030f40009112381340a9410f9400500b07141140700514076202500600a04e000c4803a40e105008041c1201206140c0d20b00d203006a035405881d8a241c00d040004125040c41c0001d006e03d860070000e0a1314000c003058080c0f0360740d4005100284549941800c600c10650841c1401400f40d00340c091003000f0000c004980912780204d019100d5205806010300112042d100e40b68060600350300700700c00060f0790101908054071407240c0c1c0078051812100c1092143c0ca0f0305d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 527831591 1250 527830341 527830357
    0xc0708150a0f0218010c170d05060a0e070c0f020307050d081306030b1507230607030f1109090403090305160509150328300801050a060f02030705060f011a 68
    0x1084d01c0c6450100d5014101c8142d803d070041d00c3c28041110700403000f5403940d200039014549140c9440900015040a00910029001c224070205c0c0610300703403500030090807100c88060300706580b4601c50300554409101d10300207000042c06d5403c900140d800c1c8000c180d8004113506170f48400c25032000411910a100303116040d640181000c10700121081034460720f8002030416500303100c130080d810000f13030300c04a11a910382d91264080c106914100c0c001600f00c601c40040646854100301308400958112003c951a10300210741c944015221401d04698141458000401620800c0040c0d1003c42c600d01d4030504880302121036a00c1035076881610013185024201c0141c142c5c1c003030700c4580c20741d1000c2c3c09540e007e00801c101c55006a002a2903031295040310160440c001d007044004461020380300202c5040b00041e07420070311206e515110104810721051711507101080640000030201d14400c2c812205000d03001000c54400342000c40145501742003c1c401e043c854030481c0e00441d014031181c0140c40c058 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 527832841 1250 527831591 527831617
    0x103060527071203020c092d011412031b0313050a08120c100906050712050402030a02011d0a1508010f0303020312130b0702010b010e040e030d020c0708150a0f02 71
    0x2d1482d1903481c400842c0c1421044003540680750000c0200d46401c0c410f107110306c01e028900089044121482000c004071140070b9041d5040710300c014020040e07103c88a07803501a0585410607454041c0e280e1504501403400d500c401400c074003004001c803450010181c81c0240b07a44c1506580240d64030300b04212541c0511405e1050b401c072005004e10b40040c0d4001c1c229040700703481600c15123a18240701004548211032708480301551103003844a0075a03c01d4006d4010000001c042209040030340020b40e55240f0b0290007030401c403a180e003940c4030b119000800f1107400130240240700d0081e00c43e08000c4000b00d041c00040e001825000000600c3d00907444c00f1011660107402840c90080308041880400344028420180b02e5081a03810000452003000385100304250340c0005408440f00d00010442c1914400d0244134a081101541044802204031000d00300c01001c01660340e0450184203051007110b41c414a80741c0640325074a003900e46039030b510341c0c0f168600240801502c0844a00141280141c030780c06281 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 527834091 1250 527832841 527832853
    0xd09141f020d0e1507090e010302011205062d03100908180303040b210a020408120306040902100801060210021e090406030602160501060b0a0e0105071a0103060527 72
    0x3454096402445100c40000c40400d40384882000103203407808400005003000c4031a8108070000754802140c0d0090490340031041100d525640000b8413035807400303e07241c030080d86d6000421015600c4250f001007520180c0b22002050442411440c001030790300c400c450280c025000e981c0c034034003500d12411155540c0000b0ba2403c0140180391401d0141d12580310b15010310007000042041c21804000d804c0c10b082640d030180d03c1c000c094050100c4564054000340002d4018001030119090220709200040031100c94940c0303907a110170004015000c6500f000c2d402414003a600c0181581c008a40ca06a40458080302c2c0042021200c910403841000400d50581e0090013109000010b464010b00d01440014408a0b0b03076512916920101c0e4030611007000d134001d40070688010800c081c0030381001009041c1e0000d0402c01c5d04000502601c0d8001c5410f810400c00281101c100226241c0d103880303400d450310701c01d400e135070f16407030aa8000c00742901d0000020b24580d024100e10001208a00c004c58100409055 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 527835341 1250 527834091 527834143
    0x27010e060a110f0715110d1a010203030c1305040e03030714040b030c160209010e0601110307051213080a0606181b14090301050f0109050709080d20030d0914 69
    0x2160080d54040f5040f5101301410f00342441c1c04e01411031b030704030460740b05a0b5400b0f030010300008541d0b6031300607841407004a00081040f681c012098aa100c50f00001655071041030211130007008110382c200ea9030061401d4080b4100b01000000f451158020f81c4544c03150320005490501035004034824441c6500c02000055080301d402e0014044a40440c1c40700740880c0c03034039400a01801801d13082142040c0d4013a007086000d6070b1240800384103140c0040514500030007502d80c01d032201c15110b0700c25100132002071924481100e00310b042005015090548102150504e040c601400b464400d940344514a81c0300641549030522649405c00000742c1c111030180450b040981d15107400340c014805c0c4000510102133240c50038069184034078212000c0c00403a40c10071198a0445400de0041820403030384c00400c2c41944000a801030900415081c000080c40e1160b0030008610340403092001c02c1c0c000402c3c0182080c50b5500254030152184000d08079240e240000705a803100c5682c0707a100c900522400c590 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 527836591 1250 527835341 527835367
    0xb03060c0706050f042013020313020901150207090b060f040602151014090604020405042c0303041a09100c02030901141603180b04060f0807020c0108070827010e060a11 74
    0x80303d1b058050710100204165400d110700300e8004948481050800d80c60300c1c0d08502e000f00240340509516252940c007403003040c030300075940c1029000758110f282c2c2c0d4041100701039444c1b100752180c10144003110b0b9940c035103c0703400030b454816080d044000d000c82d12020440096040c0142d80945e00c0d500250008c401c4030100300031030010080c04c942d130441da003000040713850703201d90003061520030380a1011100c1d180c1428101c07500307140300c0a6128040d041030050000241060109038090f1090546880498880c070601608000301384111400c00b51401009001c4540c011028003a5410b00341c9400c00305041403039802c400c600c904004880007281f40750088000a000361074082d4070740c10b007141c4811095241d0200040c16801034010780c3c003003500003c012039000d0b840214150b200c40350b440500004803601002800380b0001810490034028020001031881c00260080704104850350b014020841d840304d2124000d001500404d01280100300008054032260b01404181d54941c0040c9481e0140c115192 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 527837841 1250 527836591 527836643
    0xb070303050a0b151e07080a050706020c07090603110a03261b0c12030c0303041401090c0609081209030303010915030807030e13050f070e040b03060c0706050f04 71
    0x1803441c0d50f40c0c460b405620341d113a01c10203040800c00c1e00c0c0c9032a6560006080c01800030700000b02e0080c1e10204001820010b000d1506813a20381c2854107245807030f101c00b403400c94045d002d4441c5610180c42590400501040355070890011680100d010107070902481c4280300e1540f4082c00040c0801401d500f0801207000c040c040f100c41c50703001d6003000382002180036030300d40307601400004005503034001c0f10b44055034682068a48480d20403d00158600410341001075220f01000748003030440d1071200f442d17100307588081d001030308201c1d07010f50030341003054444002170051070541c068010140302d070103c2c1000c01d494007030850701c451400800031341c2560703e86075003030020707144e401001980c042184100100080408024011942c0300f0388503442c10050400078403240039060510b0122007420007090011814410354659080b000500d400c515001c801e00102d00a4030340d080080390944a010104540c022510001c0e0a516104000500c019240c0f5501c0800e2454259805401c0502c02c2c0c0c00b0f02e281205402c61 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 527839091 1250 527837841 527837851
    0xf0d2006040f0b13050121050c04080f0714040218130204030c06020c011b03050a110c060703080a0b01080103031227081801090f050402030c0f03130c050306010b07030305 75
    0x3640345070686424240d14a10219840410064400b08008504d8840080081c02070030080ca040c0262100507a00548450342d036203d00d80b1141c4d520408950f1a480314800c40740540364020407610324204c0c0c001c10780c2c0c2e41c1c200c0340318a407041c2002350480e030b51615090084812001c1c50f4400262210442006c002d01c2207000d21407d0800c540c20040000050203056011008207400c1d00508141034a2500142c414207004d00c0441c040380c0b108505100007500042680d041c5102e610f0415503600e00050308030718000f11110300300ea108501040d440209a44200c086100d52442030040c02600c9114006503242c40e02030000401207661800c031039200704440d41c440058900e83d400142c5800406940c0a5100303850750714103031144c58002611031410f08070205180040781d02071070181c6146141050310924880c1c9070090500c91500080850307d0221507409403400344003d884e00564a00f0145000e034007008000000b155004104000003500b0b24001c40d03454101d5403403413069480c10680765011401400c006207 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 527840341 1250 527839091 527839099
    0x150e040b01081b03090307230601080304061209060b04050a0b0f030303010806040308042603061e150903030c070e10081b06090111060a05091e0316080f0304110f0d20 73
    0x302c0700070580c041003080010890b088c01c2c0195440e1540d1141c14901c050b007000681b580304001c1000b00f0365201136403143c2c4e098201070003e080c50142c80e01d10003414030041740951080c245000d22500352021780c000301c0441c200300e5039802e043c07000e20281a22800244240195504404001004a4002d11f400390f0301612032960014480210721844404004080010020314800b10070408281480c1e0170800b0079000000f10381c103403600b905000503101d0348a05007040d907034800441c03460813940381042070b50031000680056a5443d40c17281908104680d04840d07415008945503c00148204081003242100107a071090000327601c1781105002d1a07520182e02e050402c40018110742c21000148991030040c6220100410300e0b0400c0b94101e843d0404084842e11400943e8920b22034040b000011034500c815126920201402a4109003030503006101086820035000001c0100f01715140301083c54036401102d031420404a600180500500d00510061a4010190006000b10402624080f40b018010 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 527841591 1250 527840341 527840347
    0x2160605071403120402040c02030c0c120f060a091208132012060f01050a06050702241602240904090606080d0c06060501080f0a0f06150e040b01081b030903 69
    0xa500340c0f0355481200003c9060134000240700451401d4040c0c0c1036566081e01c0210b082031102404141c5811068989610401a01c07801e070403203100600207249007c0c2013405898080c580008040e0140c9034000782150017039103a0800c083c581d809240d84078002c50000c024a41032a0003070381c0b40c0b9042a40103403c42c450600c110b0311146903903a8500801008240038001c1c1a2904182c100c8181403003040c0c01c00c82c0f2980d040350b0f040c0080b0354080c041d52061034048441c00b1030ba586140e00076030180070340606e41c0e948000005d461050740184a6415000078420781d0061000022201215a59551800e82498035a010008180369107459001000f115008080000d2010b03566923255290100d80c1e115600403400d6440c4410601802b072042c6001800d003070170800e0341898046400101d04800422202107a940d49250411080d0386510420291024074904040300701640c1000d002c1c01e10040000c0d10aa09281c22a0400d501c10906540103030305694251104199018020016420080080c01c00d0701c828 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 527842841 1250 527841591 527841623
    0x6030f110304080703080a420f0f1a1c0f061d10031119030c17010f06031709030c0a090506030d1b06050402060702090106080907060216060507 63
    0x30900460269200340780c0c26568503400c0c900030780140f00c02800d02d98254500300b070409040c5200c0342c00d0f42842244200c10515610138440d101104043d901d6010f10322641300070301050701c0d01c40650b0344007940d204041744842c071580e40400c0400060040795201c0441000d010b11301c0c050310035910341c0014143d0719801085801ca260342043c02c6819991049041c0401e0007290013520b0b100304006500001d00311902040582941c031513841c41240c0b0100c040c011102c6003000c00c400c5068102d646e02450f4800350b5292540e5640b205000b600704420011521546400446260309050744168401c90ba404840c0e00c10708500b002401703000350030a866083d018001c1d503808044940d6814900c0c0b02500c10304c4400aa02e041c41800e040c0340000c4040400e0600400c600c20540c0c800c07240081c40e002c1544214041200ea5030303440801c00354050130344008d4200c0d501c07900100d10070345c210700664802c014074411a88215542c00c0e00f2a5103400b00f0054080c01d4043d0b54050050921840040a0f91401400c000701e8860f81 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 527844091 1250 527842841 527842871
    0xe030616020703140f060a0c0e0103020309070608090304030f0303020901030b0d02010903060f150305010212010806070804080307050f0310032604030b0c040b071103060703110d05220320010c0906030f 88
    0x807c903005000700e583d070f811001c0202d03017011007945001006e207411421403a05901c026910151405500d0600c00800c0c00108601d03020000c0750f000d564011189599644030340740c050301035003008032170368080381c203101c44410349003030801c4a0203140d40c0503075400c3c20309480c0d41c59040061030440e04800e96152204060840c000500400b940294800c200050340c403000200250009107041e0040c04a90b00710317a003400300c074607804043e003070b000740d00082115902d80b01d03500142c405104841103e40d00340d074003001b0001407400407038844040380e0003000303044d009c601d5060142d480000c0488007407611030b03010700042c0040780c502030b000c0e648140c1400d0740ca441c0c940c071440c0c0002560010304c8211840c400704078030481241400c2c000990001610308080c031540720f44400111450064950704102180e540d80050854400303d12900d172b40c0d5611590b00100c2d0035207824001d0183c01c0040d040080aa4281d4038a140c1d03400501c180074034121a40d942c1414241080310443c080d102c0152004105c9032160751001c05440 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 527845341 1250 527844091 527844103
    0x40c1b0302060603100c0f050a020109060c0c0c0819031107030503030c030a0b030601150509041d0a05120703020a0b07050c1c0210090804050f06070609030e030616020703140f 77
    0x4040d030001c04043c42c01c04105454009416000d41a0300e041441c5241074039045044004c1c0b1080b141840e40e100d0070300d080f00324010310100d0009080241003010040c4002c4c0c00c02c8181880c640500381c0c202d00d181e1140350b865030b03403589040c007a06030760102807228002c03a116058904203104680140d4103802d42c1e030b80315289142c0080e207640c80d640c40000140151403d642c440e031903591a066004e05003e40c900710382210030007901c403d44010300900081481342a03860f60b0111002c1d82c0b8002440340c0020381c6241c081e075543c203425030482d194454400d0608800040500355800c1952550090141c200320780d441c2b94012001509030418000705002031407000c6814070200800b046c0a0300d00b40408108541c001349040c000c00003d032419464a10060007140c80b40d02100d050340d8050b0751600c0740500417408982603110342000900001d1074030b0710650030075500001d40b820302c060481c00c03a107680c4c68000c511614140d0040501015a10803079081000680134051356030b20b4501c0d00181d4a09581a00d4034900f041 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 527846591 1250 527845341 527845343
    0x4030b0a0c0f020105040312090501020d050a02041a0418020c030c100b011b0c0e13080408010608150c0706050402010e040203040506070f0f0813020d05102018040c1b 73
    0xd0300c80c024084560303405800d640340d60b00184000d0220b4203003624040d10384040b07004060045901e82c0400b42c107000c0c00750111100c50b840d050042060345082500507000350414080d8414070b9905e03950000156071464140e5090300e042a10b45400c21140740c45100003075124140f2030199020034018840f1464050240c5044294504000314010041070001844603043c142001e2803182d241104c1c2011508214451041d510000d51b03010160b142c40c2504980c5425040005101d1200000c001c83c0c421010342241d01191200b00494a035429200d0301c0041120341141d5000d440755050040b0400f09074035800a540050040c18480005031182001c981170b42d0080310103540642c0410103000c074440d4002da900d0100212854004051640780d0300007000c3c09400b0b45540600c19446440da01550b48440e0a0024180c1c0300d0304448042c0841180301010705a02d0940f103648005001e41218442c880c5011a6081003100c031618402c46480c108001c0108150840300b810050512401c0406006e4484c00c0b102c0c407 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 527847841 1250 527846591 527846611
    0x1060e0112170307230a0f0f0e0303160618020d03180504090614010e060303090f060903150106030b0a0510120906060603021e070b06151e0315010c050c04020f04030b 73
    0xa01c29200f080c00c81c0741d100741290002c04000b0000ca8004130380c003100300f2400700c00c41e00d070140304d8620740c8d40111628a51a03096039818000090240e005a4074194581d4141e489040240038900f6070307482c0004034a0b0b501e40042d4000004060f094001381c4a02036085541483c1d00c1615002038841c804035048a42e881070868100341d0701d00c20414201c003046490340c010f04c00310044003094074141020907101d0113014022406400444a0f028440e074507101626041d40000e8201c0d440340c2c01c000c0300031007400400c1c880c0b40046440c018080c0d03900d04040035010f0594601a000040b04542200308960f01284202c0320419260b80b0f50482d0009007450081200405499501588955009051030300b08032440c551407014800070000354000070200c0100e41d0348040101d030341c4003001d02100c02030f180d84c1c450701035000203c0100d038180240d111100405113010380c2c2d84a8076403c003488140d00541c2d481d0464038000d0300310307031100707001141e1850705400605002c4049820b40d070415660741c0e52035402041c280e4401040c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 527849091 1250 527847841 527847857
    0x70b0d0615030c1d010e040b01030b0d0303021b0c032a031b01020118050613031101060806160512011503061706250c0213180b060109060201060e0112170307 69
    0x781a910102d0940800e48000b81d00d101081d80f040044c0c0130000142646004230744425191110b6806540301450b0040081c0145a94004910b0024029800600b03509102031340101019100100095a95002c00000e0018007240c08655194903c2503400345440d80802046846501c1030b80f41440054082c0546500b46403146542500190a44120407116915104800070007408188002050f5811131015503d0516525039030400301c6003064214082c00f281c2d030810320001511000029010310a080315070b06441c1c1540e08400c203c806201c3c941280400490400060000c102c042451041e00f0019050014120760b07504c01e01900449100c0e61080160003075420405c9200800b80f81170107804054425000c0c0700a01d4801030917500c80408040c1c02807110100b2a1a00c41d019800a901099244000c1c80030b261545410f0b0074a402c1110803e0001d00764000000710345005000d59800c5d586401e4800e040c90f0300305002414030102802040e116246900200008a43e141000718040d01c0c3c0b9543c1c00103 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 527850341 1250 527849091 527849111
    0x240f100f0e010201020c0c191205030d110c0618160602010209030606040b030d05030a090b0405060403120606170901090b010609030c050906010c080315060a17090a0203070b0d061503 80
    0x3166440301c50032815640104a000303c0d000c00480c00044150048496002c80703100b240406008090681200312540c18041e80001400000406440d03e0f0042450602c54200c03e450650720600559590412a901c07120100e401189001851140c0d43e0100f0200d50700300f5442e4203c07100410312507102d4800340c0d60000e242000e0341024086143e00040c1900c0a2000c900351001196403a0100850401044408000309284202d0342e00014051500911000001e091500b0680e4442000f81c40850101317074642d000790050001400703a0300071211a40c0310303500020720081300c1070340d40c4c00000c0503165595a5004c40300d00045801041c14042c1c80e0598500024900310701c1c054a05c440282c10043c4291400d40400440703a9119904548559000b64101e4580c1c44070f070b00003070480300c0d1b850b500c9902c20300c0402c00e00c1c2540c1d40010040c008595407220004203480e500c1100752240390300700010350190081c01d0144079031400c07080180070303d0f0f5051340c00040c801d5a03107509144902030104003100003030300c44090035 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 527851591 1250 527850341 527850347
    0x330906140a0302132a020c090603030712090504022110150e04020708030a0b10030e07050d0305130308090f04050c0f03040c17030a1413050f040b060301031401060e240f100f 76
    0x804c42c42001e440c0000527090010000b5034a0182d440024840720604040d00c8085205079031034001040d000e8801d6442d134507040340c000c56481c140c000c50300780c00c088a00000c044481c101314901c22030303143c042a01c07401441d0b501c4c110b8160800c051604d8001e47c0070841d0500054414000b144100c400c1c410000d0841d298008018000d03851050440c01c05080081c412020600440c61008a400840301944071b060f02e0702e402d5a20740101c203080c0002c1070826200000740540c1034018218480d0848510303554903051810041150400d85501102006c04d00c95a0300c10030702c400007113420a0003440c91003078065540202481c080c0d80d05500c1400c60300301090300c50099800c500c201031180340c01c0b046582440f00900046546d00818031031144507100306404030226480b558011800c2103000b4001c1c0365290385030708110700740c10fa07403621040c0950310305240003480041c0f11140500500e0303200743c011079150035031088001d1650002d42e190751000c2c03001c4400c03500e41d0f10202042e12001a548401c640110f400d0409 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 527852841 1250 527851591 527851603
    0x20c1e030c07080f0d08040c0e070806011202040b090d0215161208040209060d06150b03061306030f0602030a0b130f1506090306330906140a0302132a02 67
    0x2071401c4d031050942c04040000440c2c140e40d002100e01d88a6810b40c0c96087ca100d442e483e0390700c00c10f00c000b205030034070190740d50000810b0301c100000c1c0c0310764106013a181c0d07021040303100c0d034424400064400d2024810030710b000c0b405a15213500090042000c612a030740b20440c4c1c4d0b480000501c4d101200c1e11a8101049220848450503844608080101e403a05401140001790010500c510405449080c0810003000e035000b028407040e09812101c0701a00c030007860b01540d00c140c0307401e442554070041460031100b880c020501aa5445903582041c4249951780d040a0b4002900b0115a280c4500130011651113a400740742c0000c0d180100031500300106641807084441050b4082c4417004010401e10559411101300012a80d116200169121500034400700302d4120103401c4002c03068030301081c410082564941402d0700c6052204010403940c0e05000301190302c1360789111b60424203034101040545031081784007803144a100b030040755000103031800001c0c00c402d0314080e41002080c2001c0d280015810008 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 527854091 1250 527852841 527852849
    0x32f16050f0601081204050d11010c12111009121404120c032906060715050f040c06020715030e0f0d08010815091203040311030403030c11010e0112020c1e030c07 71
    0x580d1801f0300b810003040b2194a00c10b400341800c80d024141d00c810741d1061413464086500400c00390b210390240007000700300b401c1c101c406040304d104058412980c64928459107200b56480038205501150b00d04081d03601150134031026104080601000425110103044048100d2040c60304440e03040c110326141c0c0c1e035010403120080301210784a0b00802c07410341d203000b41500030004468080d01c4864a160403075501c00d8043c00c000310281003006000e844c004d070494180c0624803504115507682d44901d0100c1c0d0b903455034070840010050340e440c03220182e0f00991208002944140584074064140c4d039025240280c1441e05400040c01500100544002404081694449010590298202a00d01560b244240c03801110368020010114080602504801c900451004243c0342c44a544e0f00b405041e500046800b0707200f0907100001407450703620030200c07044001c0d03050b1101520700d0f4600403c540250000c0143d90f0840c130030145082d089882c0080f403511240904c100442ea01c0e50030520302400e111007648 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 527855341 1250 527854091 527854123
    0x90804181409162304090b070e1e010509040e0d02101a0a03060b030a020d1a06040b03030d0905010f02041e06030b01050d052203020c01032f16050f060108 68
    0x322520303400280410080413038904003060800400c0c149000300240e41840c60141d485031400099104104418807814401c007040e494040c100240351091004070700e1a50840f9050404418100e102d540c080c43c0a451002000f406c0020001488101c061a1504444000d8056032040202c0184502c03603000c1d80e020305003444900049580c0d03101c00308400d40380d5030200420168442d44180210b403420440b4940f1280c00030800d61a0407410704001407110b45080a1000c0c003081140001c401381820700800000402c09001180760140d842d44140040950719000c036003c0d502c421440c020342645002400251011204035109899217140b0b445540c0d60990280c0c061505003000c040450703030031400303884456407003078004540c40d83c03103102c020700c1840111905407951805075105030915500082c003410400081c0c9040140c41645031003107825030603600c5042d004981c00c0d01d111400154030005405000581c40d40d00f401080c503070740ca513400d004102214060980c03208004016040c1c0421016a40083d000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 527856591 1250 527855341 527855353
    0x706030c0e061e03191103040305070206030a0905010632010219061e06140409050d030c140403030203030702061005010509042c0102030612060609010306090804181409 74
    0x104003508803100c1085503449007501180b5010020f00700300041c4420010142c05940d68500380060341d01a45400c5d80122515190008000143c017000301100d00442e010748680341030022503400c002da60b1344010001aa4039032513000110020318240510303c00b0b0042c984011914040301c4001400b010040082e204600d03016000410303c1d131b60040744601c40110040b550302140440e600b49000a01243e13008162613072881d82145061a00300d600074030a4800c208103006ca5040003c04020589000000103030113500325010f14207a0500a51003240704c8501420002c8511104c21800f1001e40c00c81e62050780560800010004c80a0341440030300e6111081160200a1505010008180e40a42c920b10741c003031613540320495900d5011072980030801320442a100030440c011021617010f03400c1516030600802c07040b40c0d1800760f2080400c0307a0340b00304009411720a1503031a42d1180400b4005241050340c6401d010000840c0c1c0070f9440c0d0004904440c0d0807401b15840030074100d08103280d00001c2604000b07070000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 527857841 1250 527856591 527856611
    0x15090a02180d200303120705042c012304060801141b040614040e0403020a03080a0204140d0c0b0d0c021e150903040807081c030e0721061409070603 65
    0xc02100ba081940d00388144401c0c003e0240401d241d80705503d151044400c0500806c20225030010082c82900c81d0160550260a0740400b0012507d070801c80300740500c8055401400300046040d04690342c10f0031813400072030343d51500300031400b140c2e6039400c1780c0202e9440d241001c51441c1c0382408250002695003100101410b1120507200301d02480c000c0c08104042d8103c10a4031810a60544018148145c07048115003040d14001e0744d0364168030412004501c0d40000501c2e0b1034640e100351303412148103070a01107940f0340440070003100c5885503038110f4034000500c0d004184070340444041c08060b800d0580001e0720014510000c0d107040d040c18083c450717024008840d0703100c0002c00314003c0880050806c00e02950788581201605500550708488810300c02e00000103103883c0d000441d0000400009107034043d0400d0100c04405450700040e0074202ca030701c00c56007040324590910003140840d20008032a605009030303035a6a8140ca0001e69805850080201400700c400400d01216000b4034440c101001903c40ea = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 527859091 1250 527857841 527857853
    0xc0703050307050c07031703090609011e11040b03131a0105060f1b030f0403060501050405090304030f30110d08071b08040905010816030f0b15090a02180d 68
    0x30910303003c2000c0030840941d2110b082100d84007460341f00600054a04100f405030b01e5942089440700d503e80b0524001c69008038040c07042c08011001d101d5082e0741407080103034040150020000848104e10100000928500024051402811845018004804103040c07001d4200050710701c1550303d0b05420010046980d41d1411601c0050040450648a14100800881130a001080c0728a24040001d0102c031912001c1e0051054078462201009140d89070400e00088039800c0b030b501d078201e41c003c0000b40042003c0f404480381051250440050103102220244002c1c4401050044082e0680541c540503a4200040d10080d1821100a201001d07080a00610144002d050441444042ca014820030034178140c800c60661780102e0401d507070f1075540e10500001e100034400d0b11164011080c3c40241c2c031282d140031108582c4c02c4084c0451010080d1148441114007400103c182d0040a980407603a44802d0345291040003015001602da0111464405070249202c00461080c002c400c462800601 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 527860341 1250 527859091 527859097
    0x91103060d0204090c06270e012709081b0309090114030a1a0f0907030f080a21050702010b010c1a0727080d0503010602060a0902011b0b0406050c070305 67
    0x4003110708020246007400410020002d103d000b0384a1040601c011070040c0d002030900c100301c480d020803007a141481a80c060301c04c2107240648c00354114200e00410242560741001420003e000c5901a10419003600000c00c44032140380498ad40500410443e002ca44004d045408000c01c00c0007640c0340410b244c000514003d41401440c000c070200f0f030443c00d540d480420101c014517030310a1440c0314111100c51801007040703003111038101c101260000210304543c08201714080b0380c7c0c040b0700380c1c030f0704a210b07038032005280c10070304d281010040c111507040707a801d01c0900c048140d1441c40c01c00080900b011800242034070a082002d5052106546868000584404040319070055040c0d80140350340300c011044075204603040780081b4640d0f483c031000e940c40002880000c01c82da540c404031206c0e03858180059a450009100703040258100c90b001448901c15500206030300f900c140742245e00210003510104031148000030565009507203404100030040c0e00d1054981240d400402d90b82401030070380e4001d100e48 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 527861591 1250 527860341 527860351
    0x10801090e1f020405041d01051510030b0d02060a1112030606090d0510020c07080118030e09040507170718060f0303050d0603080708030a05160906140c010e0c0a091103 74
    0x150307030742c0c454161080c059050714003400c1c1c010002e001803611450207801140400b404010b481d440c0c02d0100303030700d010100f80c1f0109020014115080b800400394041e001003082a040b5908840c001c110b40e00160351302c40080000c2191a226581400302c0100340d2803800300c04101901c05403400304144001595550141c1e040d0410480ea60244a10ba40c07800509040c0300c4c050310002c0500100317003170864120200382001560301d0500204242d4460000c1262160185200034001c150300801440f0786081c44140940e02502800850b0f080035a51100114035600480c60101290400e92040c41045200e00d4021540c0300044024014a814802a004802aa4031008052200009260b07e400030103401c01801190404e00142d03d40d901800d0800c4103600803075010215500d00400078a03000107080e015000c0000c1580c40c13407180b80c103055090780c8480c0044c1d10ba18007840140b2a03024040b009000da00300c50005080a401da84602c20b0600c07000b650550002c6260600708080810400000804d881e800 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 527862841 1250 527861591 527861623
    0x4051603030813150e07051f05030a0e0c03060a020d15051807020a05010c0504140612071101020708070c1523030406020c031305010801090c050f030603160f0302010801090e 76
    0x900f01441d00a402407203005000003043c0c24080d05034802c10010400e00c0407200c042e181903206244c10280160001038012070b050101e84181b0124000101907480303482c4016114044400081001e00085d01e4410111140f03840950001016090140705d07005178612120b40081010002e810980004c0298140c9004801000a00700c0098040780c802c0021694443d0404000c101c0f850004c0030052a50f40a40288490200c40c91009001400c084084400091400715030107080d4948900c11074218000800c001c1956400b480214040390950006180081c0b186180c481c00521b006402d6440c4d907802c280c0e03101441800307110b4800741d0141c0c14000926084030f03500301d07540c0d554a14101000780a0261120300a110109920003c040c041c00854155070707090303e031640140c0c4e0324200003040c1c550700581d4038002801030014141c0c0e06240c00148d90049001011b0302e20205d1145640f40b1000c105a0280024203441b100820a5580010075580500540181031044003209003500c0c0e035444410800d6404 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 527864091 1250 527862841 527862871
    0x60f0e0a0e1606030c020d081e2d01096f0902090d1509020607080a0f0219020603070c0501150302030f0703170f0c070b03040516030308 60
    0x3241c0c180301035000c1c424202d811191640e241c11000740280079006170714002d48548541520b00d20300800f0780503c03d0910204c03d141d00340d4100c4201510403000b604110055159500b82d81002020448e500c0040c00714005c1c1900719032500120505132440200002701504404c000010f021000c002c40803940c2e04030f410120342030345001c0c01ea40210390305040400010b0b20b0100e01c2a1043c034085600301c0c070003440c03440d4851520341c44103c40c80403449003485690384440340150420004800400f903061903091a10005003c40c2290007148843d032080b00c04031798803207000941160450300000260b05209803440203104958400190b41c3d41d48000d8140079214078004030002e1121840b400301c603c585ca510800900811010050f0500710b40340c1400100c0c07082c010b1100a50700f0300c40004121040b82d401c529000710307410481091141c99840500b00d5184440100b154548001081200f0001040c0c00d070705241d540e2400d0309200e4180750030302180a80310001c00108202003507028541c19045500300b8a0900 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 527865341 1250 527864091 527864111
    0x314072d0911121801050403120c020708030d0c0e030102040303020106030c06050c15150a0608060f041103010501050304051905030403020a0b070f0204020901021504050c120d02060c1606140a060f0e0a 88
    0x11041d003443c0d1360541540c00c10082200b05a84240200440c0700c0c00e400c240f203000c0c09000280e0f2508600c0c02404c034150b0041c000c1894220441d041a1103c0e80c19044c200d07038850b103c5002c01e0030f99206400c20b84c0903079180c1c41700b00304019030b0103140d034000c1400e031411a05081240d60519250b2128496110915912402040b00750100c0b03440c400341d9800003402580d110742d0300c01d0f010341103241c201c07003c612840389044003200c2c9007860f000d224413009032000c503940307180c0c04c0800565a5802c09042514148107084403ca030036100882c0268020b0301070402113031030718610301c10003032810016008150710740828001100060081480c1c0b1045a50464003d0381710215100100d1500b400c3ca02d0550000e28030009000c14401c010491f208100d40a40e40200407114003803030640d03165010f50031100164043c00c00105201c2c802e20240001c2902220108490720082e00c0c2d0740c05441401b1201440e808441041c071038640300c6482140024031203862440002803401100c404c0400c002030060348a10b44914081d0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 527866591 1250 527865341 527865361
    0x100503061515040902160201260402091302031f06060314041205091305090d081e0c040b0f130e060303070305070c0522050714040314072d091112 64
    0x14004e045501d00071500c51300303402c030a020050304544007030780810305407080064150102004194440c83d169000c07051600c45500303011041100410200f00918441c0704600161b9080c4409000b070a00d00c4000c16800440036000000c4503140d5115000345450f0412506c010750645494030b2303129800c9251003e0645010340181c0b42031040160f000d910800d0011000b0450f4442d0384154064808442124813402ba81c0b80161504c840030b8420601454041d03c5520700520100d0b0501e6024180e400c5450038603907256050101e503004021402c02d80c000200340d00c80c2d0407a010640f00c005200945024402d0b04113140030079103d110361000501001030002e2400c0602c140c3d8006c54000b000003901001001144010301016142149945100c15040801040c8024480c49026022001e40c80c03240f485d09145984c2c3c4052003454400d8003c0034090b004000412151028080003d103450442d0010038804802d90000241400d4010184803840e00342c0d502c1103c0c0c0c0c400c1c02e0340d42d2400884141c00041d260b0303021517 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 527867841 1250 527866591 527866597
    0x50f010f060522090c03060b09151b03071a060315061c0b010e010302090c0a080106050a2c0a062c0a030b0411103605060f03100503061515 61
    0x3c0c000b81418018006004005030748000210106a41e0401042d911080341c50560700c160000c50b030b40074005050f48514284906d0007001c58009010302d01c2e0a8540500046065170400395064464241114480007664841404140d000b0012000780c560020100c008855600700544241d02030201c51205000360342d014001c01c0714807504407e22034007a41e9a040ca6650301d072130901040b4020380101012500442d1381d002619445d03003e54a511043d81e0910f441120030382c0040c03d07154104507104c00f2414541108000701c1c050504001c20040d0001a41c109004c81c400380c075030010b010098008074403000c4000c4910141001c1c3d244440c40300769060344000041c50f00d6034a41001e03040034003a000348020000504078400c0c02c3c1000740c417448110700c0c041b10141ca1840110000d2000c01c0342e0760003d6114600d000707000704030002004070800a078641b00d00c0812142c2c0c00c00440145902400020301c030f110841658180005c2608a000b0840ca1400340580100e0245072800140111610386c81c900744003a01c101a = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 527869091 1250 527867841 527867887
    0x212030a0c06110f0d0c0e0303070f06020d090605070305010501030b19030224030a020309162105030d060303050d05011505071b09020a0e040b0a0f030b19090f06050f010f0605 77
    0x17074482140016410041c80c5180e0a9408034100e4805040141030210035102241d40118015032424a191100e801035072020800800d0719607144040000554a840f650380919000e5800285540c1001c001404071400c2c503802c148507008041c03424801520381c000704170540f40e043d40d0185d01240c45040281c04c000e01034140513000c0c200841000000200d90b800740d44111140340880d050f107841240c3d001c40d241c1d2240903041400300320b02010040a408440d6498645210390b084a15140380c0000c05021219250011000540d000070301d21383e640007a00a583c0074100d07503c11031016000b4500098194401d090b001425081514403a4400e0b1345000c030240c0061821400035582c910301000c00070400030051142601c0340746820000c032490700b0901d0044094030b1a81c00c142c0c00300c0e800d517240c40b4095507008000504035a04000030b0030000106001340b0b40e00521982c280482200340d441c0030010340708028240f0010500400c01000800fa05801c040102c0302142401a80c800342150040b83c1880c1080b4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 527870341 1250 527869091 527869117
    0x90a1502070501090b071202040303080f04051501150801050405150907020c1504051e090c13090204060c050708060403020c0d3f0903020607120522030212030a0c0611 73
    0x240d59000d1002e8084258401c050711f640d002030004405246d241240074070b02014001410507400103501c5540075646917049805407040b03420000e980140c0b4501c1e18400d81023001c94007030710081055146d0300002c04c0340c05440121001c0c403e0b81351202040c2810458022890b104541c0300c808102014003c2c0f040c0300040380d0260416902c0060040e81e142e0760f510503c2207500070760307174205071180610000d00030808010004003440078076214514440e0a41d044400404011a02000005240700c42c80c401080205440d03100d01d88600041e0800c1802c08201303030f10042c8990807150400c00000d90200b2895026401212456141081da040035121002e41202001e200800d4402c2000a064074071070406500c84503846424a40643d0401122607100e01e01c0020f4000b40709004c584001b4050445400c1c044c480352900c0c50503d4000d201100b0b0420425040014100d2072600500035824a400d1281074044444029031420003200002049081030110141c007250340d0700c9000c3ca602402e4030803120080c45100c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 527871591 1250 527870341 527870351
    0x207021f020d0e090708010324180309080a030c03210f0e0606010903030203090405070e15090a0b090f15091003020c060f100b0306040b2106060108090a1502070501 72
    0x400c001e99141001100100810020a9184582c0c41c0038141c240c4145c04560310b48089900e141c3d20310303030506400c4251030001c1580713103d104070a8540344030380f0301421001346100c03010104909001d80b50b120306800441d4550414000007010a0300306581c00d4400d941490588450b000010a00c101041c4d60009800c0c0c07507083c466101075040050300602ca12107400001c0d120720341c69403030042d601101548030050168005000d589c1035440e1a6000503440903035030406410349482e0200040345600c040f0a0418819004981c034505400c2411402020303190010106260811400020360904905141603100300e803002c81030f0391590070071820750364880380240010074104081103015010307400440407014213204034000151070210700c09145001c1d54108525003106401c0600f41c4005078401001e8135049520703002c424880c0c0c0c81e81115500c0500100c200401c420038020720039030031300d10090240380c10020140103211074540049100d0724004d9104140c82c100301107800403d03010b40540c4401400651903c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 527872841 1250 527871591 527871649
    0x812070609150c0e030712034407050a080c07030329120c0d20030d0f020c030703020a140d06020417060912070b0c1306050c1009080d020702 62
    0x540040c0f20b4000390f6100e0024400460062540d00c0e9818450030402d090029070140209000d1410b4000e0007a050011101c0c4d2003d030540c200d00000305450b040624403440c020904042d0300f000000360442c501c0e01c0d0031071070060202002813070043d01904205504600003400c508040c00b0398000d52140c80001441000f9214172040c114100c0e10450700d80780640d0807850041007024000c02d9500003084000c00003240d40025480765451030a610350128414910360712003050503901049010107031400e6540b4010794642020000703040041341890700e4020b9220388401d10043c3c1d298800d800a449800240c0740c40c44082d01c001035581f400740c3c0703006001c45100003404a4270b01c0c07500114000c4924000c00302c40300c0340c03101400a85d83c2c090396004a0800c5406010403000a8072032111680c01c41d28101c40e40342040a17a030180710580501d9800880851070000d0301c48282201401944550700720303480c04001041d03207a19840111300c13070300c525114076540c0090907604541c2d410407100b00504041c040315040c0204 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 527874091 1250 527872841 527872883
    0x270a0c0e1005010809030409110c070e0604140f0f0916080a0506010803121303050909100509011512020f13061101050a0603020d02040509330609010812070609 70
    0x30a54000c1072034500d4150214495000e00006030013075000400451070700307144c00300d120010080409898901c000801035410780fa001005583e004e030070191104800c5007841e4080204440d544034016036400708040811031940200c0e405a54481a4101592050343e510300c1c0403414030048540f84003114030040e00c040764210b0005541c5600310703c55411101540d03203403054590b07a03008818098008803070a0300000c400080b1110403240aa00c070381083c5041070068000210300d8042260100c014200c0114100003900d4591096401454161b0f0301e2141540c0d800c07001442c00f10b040c071044c0c1640e0780000d04911318480b800704840030b070b900c1d0008c103001040d00c0f05e034002d068520400d0381c10410341c28400800d000c01824803d40040b254003c0c41d03032640c0d03a03841d4240b0000e010020184449409414412503100071031004400c1d52404a01009a581001d10b10820304000044e29080c005c0010300010301207682e000400209c07000c0c00140454840e400c52038000082c0107510f80050001c0201006908030300c0d030b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 527875341 1250 527874091 527874119
    0x11040c0203040905100f091104030b280b3f100b010f0906081f1502070e06030304170709060306060e180316030309080a090e0906270a0c 60
    0xd800411300041d2900046444a01c110340540000500380d11000c00881d0050344c854440d01d201c000305141410340d2031b1541150914202d6918a542982c0150188101c04050f414106110403402c10000b140002d00130881000152a400818030f8400254648110300610207242008a402d4661100030f0080030b02c03901e4128030060400702030b003001d1000040d90f02a2508500b044500d549103001036203414000c5a0400700940051000300c404c0541000b881c2090360b8171006441064421900c1280c020070003840d140080c0d000300b00c0c001000c024001513a401004681c03c4803000c0300802d8a48124030070140c200710540d40f0600e00d06203072000010400c00d445d0000000c031a05c82075801d52581d52401c01c1c078492450144260341c0398004006811000342c0308409482c80a01078075000850038825a5045616803085c0d80e5200850040c1c401000200442c4507100e0b4002691740182c0318500340700494600611080202809481410084540d050410407180070942e40005000003c190744900008100c1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 527876591 1250 527875341 527875349
    0x2c0d0305070507060c0f0201050a110d0f14090d08030405121c0b0d030c060c090317030603012a030b060f03130b010b07050624060703050901120504021c11040c020304 73
    0x700480f40005541405032004640301e94021596403404a030a41c011101a440315500b40140840042070f545440c0c0301300600c1401d00b1003a1501d03542c000701d110001e844407030011042110f0002c108288082d0742c4503510045c1c01198084040c940303070f440303030304e4458240381c6d059144001009000c03c01c54452141d40e90b51a924420f40c02e0100010311a110502c2a040e84030340008d008120300400d600300084582d07000ca00b2140c494500788200545941c0c9104611800d0983d0010494022045c88030a10f1300b8807030380203414190b43c00b85829032503004a1124a81b80030084505065484045c0358980d00c07010304503050782c008495019524605859000c40b40e41c85242c00790707074004d40d0000229542032440201d9007000d4100e002000c0b40c1c1d507400241da0990516a8403d95407000c2c2a0703115009850f00e00c080c0a042d0700c46c1e19880c3c2c55520310400102030084080c2c514500c14201024400903840b0081046242d900c41440e90b2800e20341d03400c04400008002c40000d07081807529400d100031942c044040c0c001d40e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 527877697 1106 527876591 527876593
    0xf060c03180f03030302190203041a0711040207050105040614060307090e1212010e060102121804150803070317010e18160b0a0e0406062c0d03050705 66
    0xb0a16882100030070b80220f907641c01002c1220381b901c2d20000d14801142841d150204540030450a141c001b4071285000400409004d409c162113221003502030300c10b550301c9040b440c3c1180204003c0f80c040c0d824528025640d01d00e002c0030b00e00d1a0140754010010441d003810503d004004201c0e0f50780011803441400d01c04400d05840b00007504006440710411242076141c43c0350300b9061500180428115044002c0406c0001c0b545420358a20310700e064104c07030607040c28201082c014612040d692105c140f0340341e00044d08600c008001d012a07031083c2d036540c219032441b102c0c0b03c44401d428060441502400310001d110b41825030b10180c0000c0216084400e08001c909803c82d1032410b0f500a1140e03403200060140c035003a0440b140c07407070040b0192420804a4a0200e004002e21228512103805450031030b2910300c01e8844980b50031280e2001002c0103038006803407038080d0842d44040c00840e05 = true := by decide +kernel

theorem cover : BRFrame.Cov 527697841 527877697 := by
  have h0 := BRFrame.cov_init 527697841
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527697841 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 527697841 ≤ n) (h2 : n < 527877697) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
