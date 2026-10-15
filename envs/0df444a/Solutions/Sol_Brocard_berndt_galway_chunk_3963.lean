-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3963
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:10:59.943788+00:00
-- url     : https://prove2.me/submissions/f7e9a994-bede-4010-aa68-995e581d7e94

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 712589928 ≤ n < 712769784 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 712591178 1250 712589928 712589951
    0x708040f06051b0a050604020907111e010b0a051c0804120305181f08191505040507050c03040302091905090f060a060b3001030614180d1101 62
    0x498140e40d0004000071030000b558025040150b4095807445a680c014000804540e00e41598036039000d00301030b11944121001c9a0f100340141c41d24140404241d00350744078031510340d80113000b00e03c0300700905206500744101138009103000700000040c1d42c001007552200d0269a410300e4007035004c0310000c0b01c09040070807000c181c55500b8103042c5c0c0441d109030388040d5107000f07408803040c1700b40f1008074450260420496402100c108141c00d84c0c40e9508601d0b0100c03071555083d1458060050410303404556a00e405850301e00c00302c05883e55410f48005031401d10164549500132107841c440e541c080b0489403c244010302c01442c0c002d09071a046124008501c80060158285804961094034016181d5202e003812880740541440003d0340103a4000d010400daa00d0040a540107105c2d804031410700003908200e0b50101054030045071b404859016080110350f03105d2038a0740040034120b20001042601c0c500003845c18295603d0b800c000920f45010300103a5141e008142c90022071000400025521030706d58010 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 712592428 1250 712591178 712591199
    0x70f0813090203042001020d03090c0b0c0703060b060f041215110c0105011a040302040504171b07050301020a050412020a0b21150a0510030908031303030b040b030c0402070804 77
    0x1401c0311020042c1c2e68109440c052541030b4000d558800b0300f60f903103105089141c1e000b040882424820f07080220741900c0c2407800705e1b030200d01a04140344080001c01c01c0c600b990000980042034a21035602004006100d80c10440b590198407031880840c1030800c070078001005403070b480380380036881039049921281c8400c50a1003551200140c1d22100640466061f01c10f100900480e401066080c1f40040902c210410109162141d800b001c3d0096854001090400080e181c85802c0c4c442032186854446000d030a98116000075039101c21010b20443c240411a07103018401ca034107800d25511018034084c90420420300201c80210280c0e480310075a180040c4a0005030014254516003501d01c141c0381c0f108036038886280340081c22040014040c110346203da6203c0c40c0040b42510000c1b28489810f6078030700b001703c01508003040300030100d150100a12101500d00d50107220700a03c2618240304d4118520240000c480720551550341c55803100b020b4170b10501381680104441405408928079168640c5907644 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 712593678 1250 712592428 712592467
    0x240415020f060a1e06030201090b091f0e09100f091805010f0209010f0806030705061b25080a03081b07020924060310090c03140709060201051506070f08 67
    0x480081e03da031156002488a61003040f82484013000070007900f820b40d000240782803001d0158100002000921409a81d210920503511b10000c64050403100001e540040a600d03500c403282e8003d11103100801c085282403800c9806403124422501035a03403904440c60040e00c046019002000109500c07000030807028060480f10305e004c0316000d640c0d420341d500018080441e004042c001c0010700c4050000942d00420f007241201c0084074110f44410780c41810409647e007428141203203100c3c50300103100450200311022000501354150101c29580c8405050b112480448020001031807100001e01e0b0300c900452092079409400ca5007030800307220b540825803000c81540d99940f4240d0f4800055000560910700001104094449504600780060464010a0075025802d8950349030000c2132075442c440d50202e0001000520250070320b003058900500300d080140200710055007801e0018654102a140c1070701c1130040640101c0c0780003c2074880002003a002c5000301d40b42281042810706142c9547d2a03103 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 712594928 1250 712593678 712593691
    0x1140f06011b021009060219051b150706050a0b1206070f020c0a0608010f0b0f0f0904021611090f100501081801142a1c1103090a02240415020f06 64
    0x80b69908040c406403802c01230f55501450842c0c5216084000384001c14140025120780c04c61003c0c00c0f070303000001f490445c0a110100c03030341c160109400c41440002d40100c3e0160f106100104410750400d0280b00410604180290040e840322022928841c0b040c240c450344659148142c9105114150010b20300f8260f5600c6000060340c02001030041d04c1072001800024449450441d1524016000c0b540d2180901004007080700e0b000f0544190540300d5070100d03403101207401c000c11440f08041c81d00c285413000c0600c45034003070011580020468800c107000607000b0512040050300c064074080c01100d01540041403241c4401d400d06c0540312100742409040003010103803c41d0107040c5061100179406990f2024071014402c2c5c400c0d4080701e05081401207807414a80c1000700036030401a51a6400500305140d0804101c600000421000c10400b040744600c0510071124011640c0c0c0e000b440c0c40c6150080c001452514504000820400180483c2c3e00b04058030740c0103541d1210030b81d0b001c01d8200402200c4a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 712596178 1250 712594928 712594937
    0xe0105041e05041803031a491109010b030a0e0309132012010905041a07030606030e061608190905150708100603020c01060b04140301140f06011b0210 66
    0x2104241c0c15020720445002c47e0304c185050f9100d0324002481918a0560f454907003030b900c101c240b03003c69680c0581042c0c0110f584081991110b84001c4d460711982c114401d0781c610380660340744080c0f031604010307107070482e042000708506546030708825900800700304280c0304651008000400098450300902104800c20301000683d24001140140080410380a800148602000030b0700d110303d002e03105503066440200d00051541c2c0c50349440c1c04000c3d14045486100290202040041681904180156012036406105100203c490141c0c2c40d002a25040d85040381c3e04c83c0c0114951041d03090b01d501a2506015281942211040104446c01c6040581307094102c61000d10641c40b450381a01d07004020351030501d0a85c6000d003070802800000380111010580c0005209403490f00c2500032801070040ca80304155191f941d000b0413190007001100d90360195080c040096114100024040c3c401c1c040d49003144019520794004441c032090700c0d80501c5c0701c02110003400c070160310307104000702d6000215186c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 712597428 1250 712596178 712596221
    0x506010e0c07082a010207060506030714090a0f020403020603070507020f12061b0c0714030f0c0109060e1302070b040309080c0105090402030a0e0a03021c0e0105041e0504 75
    0x30032051100005001a2609008022a0002551030801c40b134110b041001010080007460100b02480001038000c94299800442c03d030081c40240d60003540a0030048040b1500c5507a1154400d028400d0209650350010030180040d81c001c500c0d4101444400100000600c3d041d00d907400100160402e40707001c0e00060b00807038080b04508009640c01c1d00e40380125401004507409466140c3c0e1117500503c503002101103403a03028101c100c290280d40080c1506400e070368185486011860030014014402e030300ca4441c0032555014050045844034887c40117a4407900d4003814008295002460003602a40018244206000032070462000d8248a071165142c280c0905250400601a0440d40c1105015801440c1c003144244e80190071200020819a00540c50351703140c07a42e460007081c0c5140c0340c807410700564040404042d03000c2043c0d11208822405c2d08052514031030200d420b03500302d0030010b010400400090104514021404144051034040b600c1143d40f01c4e008035047d03400e84900c01c00312811014 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 712598678 1250 712597428 712597439
    0x10206010515160210261312020a02090a14010902030403020c10090b1c050f09100902040207020901080706140301152109060509071d06010305040f0b10090f091709030118050601 78
    0x18885501194005100032041c1403407487ca41a5080114000b0488050744030300c641082d0003409180303201900205400c034a840c1a106c141c1c060241001074040308540e400000c00c8031501c134400c5d2809990164010051044c0c6a0b003400703251361049410b4402e0000020b000168035405100802403140d5080f401c0c0b0304802c01000c0c80090319806000e48a11601400c2000780c40e1000042540210403001000700720300b422400460020701c11001d000e50481c281d0800410001ca00117220400c40d000c90740d4000910001c0c041401e0f09000c00c2c0140c0c0d0000b03650a800c42c04040c45000d007080703004100d1b2800303c413115501c00080e0840d82e01100c01c42d00c00751180100203201400f030041c0c00007043c240c1c008000703403440355807001e00a59000348400d05065580010400340030200140d42d4415500910625042c20000d81103207a40f08144103a0704203e08008510403900c106024400a859000035210100f20440d84403e510b60080783d00140c0540d40c40500180d05031018542030610342c02500900030365410304 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 712599928 1250 712598678 712598717
    0x60d0e010f0c03021c051f03081809010305060c092b2105030402041a0303040806040b100803030a0e01110f071712010e06010e041d0c010206010515160210 68
    0x940c039180c28144140010103200d0245d00c000c403c2a6461240020345a80d580302c100c503503641040b0f41f0105103248903004000c000d0207800401c02c00c0c001e000d000407403188000801042440074007000b040340d0005404140e00c045144060000c0000041c00f41d80e00f10103000c103003980102e00759035040e10340c40e01c56580c6007803001c00d60500d07000401103a105088214040e00142c2688405000280102c0d9036004880200588501c80c000041000381500e658503654401140e50b800251015a44c0310700340c10224070f94041c0300041d801162460000303581540d55440003c00200b014208000c019500c44102200441c8920001e103a0130716070540c60b945400c07030f07401c0030821020078006000c02c40340c0810010540c1641366102a044400170441502603a0300c52004030f4041c450079141d02e03001070800d003048400c2c5100c100f5003c480011442215000210700c00120b0790f6240a10900d03800120b060100200810040010401480d88090808403006251b0114a0070300c00c04004000180003c02c4a04800c20760 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 712601178 1250 712599928 712599941
    0x308060f04060627030605070c290103060c1107171b060301170c04090b0603300706091703090d020a02101b020901081b030307080409050402060d0e010f 67
    0xa0700c0c104041800c062000c1c11240b842c1c00c0c0381c00b003c03440e000a07901e0555800b1040c000b56606c800107000500300020003801043e00003004a5658100030000610a4110b0046411884040300a030946034030b9900c958006160b4125408100002d1144015901e0010032012006112040307100480d101100442c40c1000034041040344806464121000c956540d00140d9041d1118004483d80f51080510414503050b03200244036003113820405050240003a03007008612030b010560544901c10b4001c5210140c440c4941120390307241209680d07290000a031000501141881880c0008a60301c6940300c15440101c68450448001400810815110402c0c0702001710020b130b078001401c1c400a19800a010540300542e004200088105d0861450f500c0d00c00700b10302c294002d8404a55561203220784d540f50b603003400301c542c0d04503461140140c1d0350400000f2500015000503905040c00e08042005014000240c810781e8050014401d40c0c100f041184203c1507114601d00c0000345a0fa00032200310180c816 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 712602428 1250 712601178 712601209
    0x1303020d0303090f0c082b111e06070e09071d0d0c03080a090f0f03020402130e04050c040b01050a08040f061e23061f02120f0715090f080a0516030806 66
    0x4028010f00d0300d4070b540120702c1f29481600d04103542c001042e00140d0b0b26148901498007030941c980f50184c09154404a0558020445651b50000c651140014800840f005882d010001007026440c030031450103550072000e11801c0101180d501080d140c6034005c14521035001690610000039840080c0740c2c10400d80001000c1c411007081e0258507000090303c01140503c4082d0141d03400080101d907444c0e442c1441405800311080d44280d41c10541812580d9101000c0058087c1c3d10b415511a5903600810903524880c2159a5980c0c06070389503981e0751034106141d40120f404a454041d44600102c3c81e100041004241840c001504100d280e01c5541224484e4405400d00b42c8501c03d00c6180e8840540e100b008130342000004001020000040340b4101c1c51508070405001c0c003140c10800d060300000240b1446005842c54074201140200f01d204507201c1a200421402c81040ca20000611507400f900710046541000d0742000c034038000709250030302c0b582d00860019003024104009868007004000c000c80 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 712603678 1250 712602428 712602463
    0x3010501050a03080d090b0103030f02010e0c060901030e0a0501230a092316081506030c100f090f0b070b0702010903050315060918010612021303020d0303090f0c08 72
    0x524100c04142c2404060101901d0010b0000b105140e564803074000c100e44a070301c040407502960f0340e800c009240c0d4092925020041d420820f0440114100061948070400002d15031031078072004a0040d07006101c03030700f05040ca43c0100018540450400e1044450005040300c2c3e00170481d00401c10405031640082406c1c1000c1c2c60100034001040741000250303203002ea00722a1a40c042815914540f51028940c1504c4494603040c2d030220301c1c0000411071003441210680c004a064039a0003c160300d44c41070000c81904422542c17480c80d902e0780304101440500300d940c01e051901036190540e03120742503020740200e05c0d15400028150200441078016552000b154070003040140080d6900601c90711024024003550414107003240c400f9510002103601900c2c004146414609a8104981100100b4031031003010440952840c0160b040600032607051803079000c2c010a0f160304560802001c4902c50800790304140c0d980107000c0000b82c1c450f0725640c019009079a08401e251600d29241e251918a201030080c3c0d0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 712604928 1250 712603678 712603681
    0x120c1407080303071409030d0201230c07030315090c0207060e0f01140a03020c0a0b060306011703120c2a0106060c020a090207061e050610031a0f010917010b0f030105 73
    0x900c008400e40703400058515202d030102c06451864a40d40c010507480c0c1f030345801006101016a90154041c8030089210b92070200d170501c448640c40584030f021102444445020007000d00080d229a200524401007505c0003402a88c4520340081181c08ac14507500144c1c1c000402400600e400c600c0c5030144c0c0e401151151a00341441000034140c3e2404185040c4842010810300e02c0b9600030703015600c0e10080d1000321541c5010a08014420ba201591001e0007401003900216056419800c0d49000124000c0110310b0101c426156a00040c3d0050003100645400e22112806544100200000c00c4c1c0c0c00310f80d084001c601802c2c90342111f0035a40610f041c0302c82e589403080140c032024015002c681a01400603100c520301d0030018064180107400c501d04130313007114820000855640c403450007003106461800b11404070f68025000c07a41c691201051181510613040581d00d0050071403020200180740c006010b5540e0401032044c1400034042c1101da1751a100032447e241445182c00443e85c10440081c0140d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 712606178 1250 712604928 712604939
    0x509072d02210711040609090c090c0203040b12040215070b0703140709030201030f2c1203040201120b280501020f0a0309050d030309080a03060e0f010e06060702010309120c1407 78
    0x1e4425043c000305113403015440c0d8001a696540000020032642d01c082c491210349207001c5c0e05d121154003614050302e1404200303041c050f100109407001d41c0d8402c41c1081c40c0592800070200b060300300500890344800e040e07022103100c0c031007030000e800e0040c802c690324481810301d08000b5064884030341c1070b020307545844c5003007059155020b000d007012a42c080c01c0c00100e40000c41e140d030000d0102e459030710700c02c003480000040f040d90348002c0300c0d0038442501c02694028032140c2c898000301d02c0207980103400244061510344503000c80754042d038030301c0070010b09850600c03108ad04008441101c4020351a01c2d0650318804110550701446178604241902d80544080080355070b002d080250580100c5006130308a00f011030402d4000c1d4014480b01d508240700c10f48400018034001c0c00390000d80151800120554046125804031607181410386103c0100c0707039055a00e05050002542006409a04240e110520380f000304400501c1d184c09250150f44250701c0403401e04054031443d513019003010156200000800a = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 712607428 1250 712606178 712606243
    0x2030a0830130318060c1403120c0a1b050304090b0f0622030c120c050915060c1e0604030906090b0a050a0504050402120a050c0708040509072d02 64
    0x24020001034400744000d00e01d0600b144d0301c58041849001101c5081c60110381d80d40c101b45418030461203041e99000340200d02d14015100e0013282095000081010702054100d50360300045c1c16411154a0000f5a42d200031070310002c07030412420151420b030000038041c0003403152802410300c8640195203050744180c1c154085041d0b4455414110b54447e0f4105013a8010391003201c6841c0110340000c00c05c2031a68070343c49405420340c1550411142d105c0d0f500070007d210b04001210070700c0381c14134080d10007035016008144001c56000502e10b00e26030180700c120301d0041821a200528030704a00c0014142032a03e860080d10307401464000740103105001c90100a00c041441c02c8440078440f5160941d207a802240d8240c840e80240d8100a6005002049030040300c03682104c014452181c0361014045a118068400d286104042d40904020030400c010310a42c00c00703008a07900102d003403030310100c8580400b006500030040480085401d9207050301d0b05803003503410030542d810340741c4150244020701965401d010 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 712608678 1250 712607428 712607431
    0x4060506060424110a061a0913030f2109050d080408070f0206090607050303060415350a0b0718150c020a03080a020f070f05060406120902030a0830 65
    0xc6090300d501404412803482884141000a040c40440c5d0700d0a400c0e10342503015184005804036054480943c070300c0c4910305034102d240511818001140b50102c00c0d1400c0343c481640d9039035007081c84a00842005090041180b4654502181c280010010000e182490514426560b640304000c07054080c0302c00306000d03000300c945080c0c0c00410b55840821600c0414610b0241e904582e61000c3c01042c1c0b0b80c240000030000754400c07103048030304100b101c0050301003030400c1c100760082990350300d00d805503440151007502c11315003809401c0d4802c400401681c00610b182180e144801c5800341d074514240044540c021841c0e140d071036400c145400c00381c1e041c42032401d20381c84090400d2041100d90301c9100159201c40c00442c01558100b2000b9688288141003c0d580c0c10700100031004038851810006082400d076010f82042d688020580b44c0f41901d80582150881c084080900c03000e030790348400f00010fa80030410920b60900c1402200c0e1a185165002d0080702803040007503005480c65005141d903544a041c085 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 712609928 1250 712608678 712608719
    0xd08060d06091a06101e0e03010b100c020a060504050310021b0d08060a06020105091b060d09030e040501080a020d0201030c020304120c030b1e1b0f12040605060604 72
    0x344840d803264103051000e8070302c8001c041c00c90246400d652181d074014070f0440d485a80140e94078016044016000c50380b02c25940c003000c41b0f0880360440c0789400e134825100c0e051858402400070400c20050800100c50004c0c0aa5640100e601030450710118142140940012300c0e0785d04159080c9031400011a4030303101c2c1c1075451805281e000540c000003e46840000243d407403402d00710340244059220160280200350382c2544201f00e20840042c0c120710500400784500441005403092039900c031440c4158407002001654031600a000301c10001d2610300c502d00c550b5000b0b0741d0b4240120070030707400c1c0004c81d40181c208400c0781d04040c1c80500035807a403000d0400e00710303030a1030000f50762a1130348001c07402c500276604542e0310410740384a41400d00c00ca1984000c2541d02420380605582c843c64000404841c19025280709082c05400080c262425211400460042d09a8031441c190294156404540c0036801c0c80620001c040c05000078071805105540c0e1000c000d58040e441e044c14500075501540050240 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 712611178 1250 712609928 712609939
    0x40b0c03040807030c1703090c0301061715090f0d030b0f0f061905040512011d01020712080a06091404060b060c03071403070c0e0f070207050607060f2703020f0d0806 73
    0x888200300d4500508652906e90081203034880c186840e407603403541c0d07151207213500c01d600f0141e020418a4900c005505507014040041c108500c81c00248180450b0003080e00c42c450141908000c0c078103005101c0c820a80340180c1d00050741054400c00c00c000701d000160002d004003500340074200b19032540c50454045400071512184d07404041641158184240e030807051300510343d01008103401005410010a041e0003000d0001070354038a400c82e900300e0042d418082c10769580e0030104100d19000c2d1081030b405c08030070a0301113011615040284152549000c950b14040c613140f08200034054548114410044219901880c0c403d5141d45541e0302d004010020744001840d1907503540100e02001200c1d1905d80c840d0340c4a4071a82e413411000420101120941c4103100840d000a855510201d51b200a840004040c50300706002522004000d00080c081181210b0b5140703054001126040c229000c10a00b003010048400e01602d1b0007030420b0707203080108a95500801c803000000d50040c00550f4409025103d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 712612428 1250 712611178 712611197
    0xd140f0a0b0f0307080102091318020d151404030210140a230106050304020111070b040e1330030209092206090f0b010501020a050a02011d0306010e040b0c0304080703 73
    0xb030352000702c0300d4907583d140c8140100058420410340240404d9001103039110340c2e14500601803c161941d104845002c2d80c0c46040840041c6011005500d0a600465441100385610388600c004c40c0c0640022241c43c1c40303054100020142e04001c0005417181d8841c081c000c44540345c80036100544046c0134001d0301500d031504008058501301c007900c80860884c4804002c1c0d41d4910024000c0d03401035405074001191661001c0b404800020300c2e60803103814281c003a291900e801e14403490030700302814050703032000401c0c00c82d00450650080c2d08145200200d16404600d41c48a89000a14002011006250040c0505803490342c0300d60f41c06500c10544940c20b89807001c412140e001d030b4044504010036561828400078180124610703c014030303a00c100c0004a4076600d4400580c1e80b6104d10b50001c1007a0303c00c0318a400154855560b40044940480c00d4022040b100c3c0002801c0c460260444050b02c01054200400d2002841c00241c0103192544040e19604040e1940502c9220b0043d01409200c80c480 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 712613678 1250 712612428 712612451
    0x9010501030b0f03060c0c120c251d1501030e060f070201020c070609060201060b160f020f13090c0e0f010b03150405011d010801060501120e12070302030d140f0a 71
    0xa00fa514050801404e40d4143d00d410403103c2855045094245001e114800b03003260030071141c5c3c08407035014590000900380c0c5030741c0442d4001c81841c0f8060606810b084003200080440d52a91800c0c0c070b01895180c00040e0789010840406850ac8a020302030405040c0fa6a0021010b0080b8541c2e411841d2041c907880b06544500c02680a48500500095140f00e5100002040d540c030484420503102140d000f40000ba58400f10320825004000c8400740d404042d4080b1000507130300c0c90b000f411180c80582490480d03810880059800d0700c42000041c001900c13144200304100c0d08040c2c4ad0046c0801ba860a606030600d09800d0341041f5050068518011000011942d4604021260300c1c0e50745008209101640e16140b00004900c03007090065034509440001181c0703404180030314815604181d40342c801a00f80c510144c07000e4070407001c03100d0b0103000d40c4444480e40d1160314001c0c14911f000350011680d4034000e200c29400c0362518815045400c480c10f090100420100b00e89507041029034001140700f80b0f11780d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 712614928 1250 712613678 712613689
    0x10030803130c2310080f040f350c0601050922030509090a0b01120b040209100e18072c0306100f12021302070f0b0c190e09010501030b 59
    0x159009440455440e5000600d12040301d5407005060109040303004001e407003c1400741d0f5a591256a002049a1000041208402005099216000d96020900b03008592648524081ea021050b680c41c014002100c41847d25100000d440b20007241042d4030708140382c106151180c0301030144512030745600d40810410078070346407149110101104c00700c1140c0c0340c91070090b08035031140d60405d002d52200000100600214400c402ca46034040e12680b41425003840310100500e010300c4016071055003840964240e0f1603221040000c254180c440250640707840c010000c58019441c120604480031604101e0b24980c42920380b40040c00f000341d2400d80608000c210b5101c40d11701c03181c40da003600c5088100040f26484205000c12035140034108014561505038001031094102c0010b034000614a003841500d4910382d000701032260151038200d058480b956255000b8aa0644041980e05d00104a00440c1140c400c0c40384461415428010a1408124003007a03c042c41482042e05166481c08060141c0d140c4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 712616178 1250 712614928 712614961
    0x7060c050c0f07060e0f031f09140a03091a041a0714010b0a060201060f0e1806130312050105090a0f0b060c10050702070305031c0603080c0f1510030803 67
    0x441e010748082500d80840785554081e0382c0700c3d500004910025401d030074284000d003180d40c41006005000988000400346062800550015103a603aa8072000300129604034070a40d0303003803412009082180036a00300140000700c07503003207510501e04590800e141c40300c00030100d40072900002c6043e40c80c01002c80c140c010502512401070590403000350045006441036100c040e0001c0c04540b501c0e1480d440c0c3e2022401c0301c0301070042000245a022080c002074043c0b5041590088070f501d003410490140a00c03203802e1a800796528170300e905002d1000300c00c164010004c00c0000650744010405585844000748100d00083d00208a45070344000311460030456400c40054440003406507651000e10f24902d0f6520b000b400240345a0b04c2c0b925011903e400d202083e000101e9801c10002c40c20320700b503020b5050b180030015a50034011030342ca0200000141c4a84080d294010030302c1c010f070584021b106096402c103c0319084607101200c1484c10004902c03074150600c0b081e80e42105046450342d54050190000c07482 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 712617428 1250 712616178 712616197
    0x906070c050a17030f092a040207060c09090e03090a090b01020f01110418060e0c1312080d050603120a0e040209061603091403030706090f0209010e07030c0c0807060c05 74
    0xb03c3e0404020700a03411009600580c09108600056075036040c0541d140d044145882d071b00f952010741c8216200d480410800e82c0d0040081006190688640c1c0b480111810109075a012940c108000c00031500e00740f01c2c6200380503a00740034601d003528940000d8000e0880b0300a41039010ba80c0d900a00052b48204124409002080020011401051500140d9400a01c00e901e40b04035001991010f0390200d010305001c5403080d2810303004030789400041c0081e80c1c03c4441460754409030007400140c1c05040d280001c02c50b5015124081d41e40200c3d00d40913042e1000104087d000340c1c07041815500e400700c000100c4100d444c85140c1041c01c03154000002e4041e108403220190701190125815130703d800c100a403440024802e03103503902456902d07603152511440030013555034160400c3c0b1003140800c03803d030004454144120301c0c0c0304540e4401d44c0050006102030304006103950013a070030001c00d541c06100305a60000281041804014503a850b100c03035118030742d0002e0100741c44210685101c0d02410540c0d2240c00e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 712618678 1250 712617428 712617443
    0x6080f090118030f020a3306030f03110307080301090504021804150c030b04063b0c0702040f0c0314100e1902040f060201050702010b12032b020c0c030705090906070c050a 75
    0x47c9841505180340c0b8121a0300707400c01c1040d03105100c8034610b100704c80c11a54411000507600c0015202550040c01840318004540030403c81100050b03e0140210f018103042d24000030700c1d0070940184405460540a14070060032003200780b0003c02d030341c41c102a51540d00034102007010408540114040e00300c2d20250364120b4289180820f41d00f10003108810025402c0000c108640821142d4002508003003140500d40010f040100f460b074030480f00141295800a000859138201140b10a0100e601d4100c840c2d0000380d6071080c0e5200300c8c04042c981e54020209a442e21212410813050000c1c014015103003580302500303008208c000d0380d01a01a07600918000c9020a2000d40ea81700c085e010b404102c912200552810080d0350541c0f0780b40e810721a5014206d0011400d0001e1486201c0d445541d500c403904100c0c01c030b4140c001402515000810003454550094042a0508404e052419940740c0040380b09406d168104084024001241e55000b0502d18068021040d6820801c2c1401440c0700c2c068a00d8 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 712619928 1250 712618678 712618703
    0x90f041b1805071404090c020129031c12020702033301080601031e02032802010e090708040f03050c06010303030e0d140d020d1506080f090118030f020a 67
    0x404041080c580082500340051140f0350f1814422910908005800740807214107010034002c4104550020540c03030703d2400001107208040344822980c0402110030b03045030300500c940e82118102401064100441d6030300c410f01c13101054802030000d85504180491003540801e9503400e40d40c00b00404288070708501c000d1000c0c2c403038404282d0071b814460981207a02c5019440006448080028018100e9410901c2c0704242c4140390707003081c000c41202c80241c1c0e041c0301d02241000d80100703d408200c022400707201032030341400145c80058060030402074071610508205003000703130f22504284900d0f40303c1c1d80003c0b46444100c03107280c20713147c0b4040d0f1500301805200d0f000001c020960160302c00107240b401001203800d98090302a00b00c41d0140f47c407000702c42d4035809204410910050b90040e1403907000c01e980104001c0e04916402c4c5114109600c1760340020100d2040c007400f50600c80340349800020240c020321141080c0241c2c64480c9289181c001c003003180760b01c800507900344203112800b48103511980c4030021 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 712621178 1250 712619928 712619939
    0x80109150302120d0206010608160c03230d06050a3b0a0f0614011d01050903030f0315010c050a0b042d0c06020d021902030c0306040c090b040b090f041b 67
    0x203a10034813201401501c198800411801d00480a180c499120201e807095502c5d0070f08412a000c1c00400c0080f014064110700c3e8141c0c03102094a988895108230409030313100c945401b09502a10130640c0028080c030548013003800324269800000034840d611003c484c0c01190010b01d5407114454230681c01204039441018840500e885410002a94240e10014020b280c2c480400c0c441c0001c07038010042c04150340074003c03020300822850701420541c050501c14140041c80c0e000c00e0956108000030b6403030030341c0003040000d00140741c242c4901d0460f00f0310388480c03000302c030342e4030290342d20300940010742105071101c0060100254034051203d080581a00411041040014044951001035045500107204840443c01c14030005100c0031904540c3d00605001070b8008100224040c011416a0140034040728850b00e074400700841c5000d41d12407060020702514042502045400100c1c25038881c80c14198084101d40d43d1032000c0d0f40025240c0d400300100d032160700c0d11764540c00085403402c032420440c8a00186 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 712622428 1250 712621178 712621183
    0x615061303060b040c03061d070908100504120806031b0d020414090d0e030a0209190207080301080f030f0f28050a0305060f03060c0a090306061502010e0d08010915030212 75
    0x703d801c00d0302d040c070100d200140d0503016a452800317440c000705001c011180d40d1140100003241c000c41c07542086449151070f641ca40b420f1075041d42564800c10384032000d000070404040c5200320083c45d545800040744c2011000282c582681c101e80c45101802d44005c1d4580c0c0e558110441540c1303600510400205a000400703a010200c121078015082c0202e16840382d015000d50280c401c5030070014090400b080341c55080100c0848081c03c03c98800348542405480d61000e880141003c5002c1c02541303031a5890a11458942048a19400d15030317001401076003000280c0c4c0d0300743ca54840405150540304c1072444010064601d40c0040c003904020480c940c500403d400a004105554050364103110951386c48051154171204040e0503a0581e0050000500350200c00020307210f08001e0b4a4048285540d81d100c0d00140da80c5504031606d20342102c06010100758092040d1070f101c0036140090f201c0006101030240400c1c8051240c0501280c0755400d1005500240044c1c401440d802001c01c0c0030350421560466 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 712623678 1250 712622428 712622441
    0x2010b03070303030b01020607020d0917120f0405090903070c031101120c120b0906180c0f07030215010923100314030d05090a050a08071e0b0901051008061506130306 73
    0x1b4054002d078408505054070211b5003000c2c25009440b8000b03d40d141c80c070350a100340e01914210082c4e0003014041d2840065450084c9000c4841c0801662611308110410000c40c0003e40b01000950080180c10f0000b014075107031104581d0048050030b2004008001038551508045c002607080380381100c4041025085500034200600a0700708006650b0700000384a60140240c0d400c543c0480c0101041c441800340d034881075802082103405a040a10f01c1040700c881d5006803801301e016070800ba140034240000c55508500400382d000c400d00441d80110404014403060038002104544694001071f402ca8441303840000459115210000030944030000307540f01e0304075188400601d81003d0103d450140005040da0072030350020040c0c20b91454558036590b05511007241142d091019894101111200100108000d4002c204980f5546050703403d036400c5035002031002ea107004124909103c07054002402d9035010959608500303544805d1400580329004075201a541c50960714008001c001e159000207 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 712624928 1250 712623678 712623701
    0x9040606030c06020a020114071b0e01030203120a0c12110a1a07020a020604090b151b25050906032107030e010903080f1b010e1f060605041502010b0307030303 70
    0x410b000351500e4040380c0300d00b142500a03000035552880324036014125801000003900c0741c804c82c1c0390644140b1561048000603400011f04100c0e0b60300400943c1000c0c8540700d0102d0240e55070500e0300d024010080d015240d041c402500440020140300c582c180215032107106003d9480403504105e81c1481d0505c811501016459114018000414113103030000650f0101581d00a142c00d080504065590004200d15031185501204c00c07014410b02c03030740c2c00b1f00038046000e03020714040e02d911701076140d1403805c81d540615041040030000c01800100018000c102503840446207654a5207807500040e10700444000340c000084040400745912100c11002001e40511139120301d1956401c80005449100d41440081c0c03284808001080703900d05058002d1258595805502c0b0780514080315507400c4031044010b074041c130b50180240044100340c0700d040000d00c510f26070081c00010708000e4010014052885103400d06051081e140c4d848138002c0d0040104401c0c085d0407521135540d41d0600074041e11700354520 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 712626178 1250 712624928 712624943
    0x3200c130606230f030c0706020d24030b2205010501060915140405010c03020f0105041104060504020412030c03021e030901031103090705060a030902030111130b0307081609050904060603 82
    0x5010340f41c1d0a4054150700000019100e0602021110b51034283c1e000400d0000c55400400c80c40d40007518510280c0070450205400150541e8081c14101059541c00c0900c0340b040800795082000034030682c10150700140350503004500d007007600480d1060340c140400c010038550a0400104095500c6141c0e6001c40d060250950346003481c82105a804060b006030411b4600005c00c41448035500a4041843c00e900c03920441d01001e109403034582c00c444090790100e0704502443c80b150f1141c0380030300034030000c2c1c10226011442d007440c3c03170385546620340454002810700c825407108805040c024003c05948030000720703203214036840c0d030018240c50303902000b150b0340443d2030407101910549405040c0c0c0d11030318400004000d16401c010421004c0c0d0041d103413003000c0644806480c40140c400b03005001c10000d807106800c2d1034a04482100081843d150080807081c1c0040c030030084400d41c08509950004001007245140c0c94603114202d03002c26003038101d81d401140c01808c4c0310411040ba8402c4084038000c084 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 712627428 1250 712626178 712626197
    0x60e010801090b071115070c0819080a0c050313080c0601030602041802030103051f020c01020a0305060a0501020f0a1e0204051519060c200a0303020319090303200c130606 75
    0x30554001c140420101c0055011401c030600e02e20000003080e8005206048ca00c07000503082d030b10b03d81198031040c14569030041000b0038200a94002d00303202e40001c02c101085c00250f4840c0402032442c0401410042400c02030340840052092070700403200c216141900341c449a40e100d01f0070b200070398054030540c03031100f18110018444020610940e4183ca50000141084100e200034160300c000300d10401d00081d9508000700d0368054400d100030580c079a0b581e140403500d40b80610810003a40d41d268031050554019128110004801048010480303034031071752840720b2250311007840703141c044030990082d042071501046c400001c001c0b02e42080c3e04201101c0c00001a41e042110a101c0b50b40c0b0f115190100e0030040304400010030000c1c403850728040707480502d25016800400240c01050552056015820003c0e81001d80b5410070000c01214035a810155071951440da00100050703d511001104190109150407000105001000f80220014a00e41d0702454152180000b403145101d10700202d0354560 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 712628678 1250 712627428 712627441
    0xf30100b0301050915010e100905150c030a140910081f0b0d09050a020301150f0f0605040510030f050c0309010b0319030f020f0604030c0c08060411060d060e010801090b 74
    0x800301c80c1a5080604550901d4031030034448064042005031141c14003024402e111001d4480c0c0e15419094120780c1d4034800d0b40e5191506000da1b0300c588201d58403c82000304804000f1080000440d19140c099180080500321070803a0151980103103c6d406600001d00b40d4514030040d8400ca2450107104a4216400800b4200440392030a0304a885032032103c040911107444800d209034000700801d4002c03000c0d5070001005034006421100700c007425401c0d07041796820500040d0704a6446c0384c06800e07002001030703515051240107081d034012440745910440821101a003041e101e500801460038080005014a0034420400e0259410440d03c010203907183c0039440d000b924000a40984200140e141d24001c4031150302c040714220941c0c00d5407401d6201f5851031050011040203041d100724080e0340d9120460781a845d0100c6940790b2540200c01c9a8004000c1c403001c90340700411030032460802c5503010790741e0000b10610750140496030300c10500381245100000c0d0a52040d044602020b104080d0000e655440c070703 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 712629928 1250 712628678 712628699
    0x8070e0702030a1d120f0601030515091203100902120610170117030415050a080a0b03031911030703030e06060406031505060103020415170c0c030f3010 67
    0x1071060100085030384c2c0c1e9051406021404080290801a00c091503013680110a545806a03401c40414650301c0740b07004106010040c80042d940a403802c52114842c10b00d0a02c01c0d50310f40d140312220194000000c0031501408103050020010400550300f50340361300a1841d8400404800c4561600038403a200b21002940d11599524122461081d0281180d07400e1440152519000e010300f500d561208110100da004038040180c5003980d07080d503402e0354806014a001b032140802801406599003040646500f541e800f005072088038000c841a103110003c5000104c5441f2680e074000c2d1000c0c00002030a000307055240d000344504207410300c102c6540307071a00700920040395450322024010904010843c000500660811900150145400f504050301c0315000750000c20b002c50901c01042e00c1e00c01c1404001c1d80245100d03482041c881310319041105009030b064881c4030300c000002a000001845014000700c200c64018140900d1208450403100301080c804c21a600382d901410346500e00c640041c1c5c0b900d11 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 712631178 1250 712629928 712629937
    0x30f050f1e09091006090f12030c0c0f08070509160e0d0c0302090a0e1c05220e1008060f01050d141504060b01030b03010b0901060f02031308070e070203 67
    0x5110019241404488241d800031076110400300c0c00220410640079039a0301c9108041c095024040203040d140d15000c40507102c0e03115540300d503100152240301000180b041c3c0c078285902640600b0103019031051843d1400d4802e510750001003410102080108a01800203059401e6800960703a030b03041034903144100743c1c0c1010842c802400040301c41c41c012403141840029001000d22440b0707444251600c950000d044100c1c1103459280c010358030081c00c09805002c200c1d807130621001c203c0d40030700d00f003040340e009000f40303e10107042c1343c9149060f00f0f91001c4a102200c44009029420400c401402d10b0314bd851180c0b0700c0b5100e484500d1040c0c5022401403d140080315040b00c8001342040940c00709a600d038481a040820403190600480c0035a00104013480042c6202e00d20130a40090405a2a000901160451220580203078034280301203909845107403c203815100c140c1001102e02220351422444d42c07017010802d0902c070552100024601500143d5a0161a02d000641e40681d844c548126940e001303 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 712632428 1250 712631178 712631197
    0x1090e011a0118080f01091a0402010c0b0c07050f1c11030d2a020d0f0314130807050f010614121b0a1509032a060f0e09070309030f05 59
    0x40310000c4010540c041c1c400586203400a0f140c990415580d0600c9900340b888690340700c00395075162104441088480a02d02c00402410118000a41051b0b000200703d4524010020501400d00011071f0603001c02c1000d40d9100741e0302c482240e0300203440e031084036218014081000070b60085000451240d0b401851a00d0703403800c851008504240e00d50060302d02800f6014001c401ca115106c0c10761001c6959400c50240c1030b811900242081802990010f185440307410380c5200301803400301c88034240540b85a409410100c0c444100c030101289081c401c0140c0315140c0014001c0c4580b8110b901d4041041d04031408884002e114505100741090511010030440c0211080329089011840004440d8801241c0c8441d0080c0000a44a468210400e00d6442c0303820a40c01048980800f001080482c030b0004405407403a4491845100c01d00703005640c00382d07480c010503060254a469610419100b1404862030312001844800c450034580070146c01072144030016070001d400340b00e44400352801041290070191 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 712633678 1250 712632428 712632461
    0x18030d0f030506010309020d0b09060703180201030b0613291e0c160603020409050604020a0c1412031509060102010e06070309020a030804060905130b0a0b18100801090e01 75
    0xc10100100c0c02400d000b82241d05059035802c180c005a04e56403140540944186282d1074141000401503162110041c00102054100300b4180541c1504d00c64540940354203080c01b0070b001c0000d000103001801030a001c003039940b921b000700041c005803030303130741c40010f000800c0c24403000b6031801c0b00b0610035104601262400c20800a80071005103102c400a15411149006568401219801d0090700f603005902c070200180d000300701440281c9080c0325442d040b9004950031490106d6141019000700701b1000b01a240c40038440e56500300002c103001880b050540c41500340c0d40c905e00a12a9500103041d8066980644217450009407a035005108644103400400010407240e965488100c000e0081030b84100d801607004103000002031600800340c0040c1141342c1740c00c0750190402041c0400301c0018900003031200d04114202200c2e0310341c08440000d5640003810340c2c1d9201a0601e1204540c1e404c40421604002c011012407055035005003014182c0b10009800c3c48902c1c1401c9a0a080c0c0380c8000c0000034a9 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 712634928 1250 712633678 712633697
    0x11703040f120809041d010b03010504020904060e15010815060102030a080f0912070b0a0b030d050f18031e0c0d050c0609010314040b010303080705070b0a0f0209060f18030d 76
    0x1408a40c2c00d072250307a200c0c80c1054500b199078804142503501400c1c03400301c0c4400303540d08080a04420b001d80c5450765005e80c0200440e18094001400640c0080e01c058000c82c0e0300e644850310284203000d9030060440340020300c04c0c60350f552020b9654868290101a151000c8607020420640c40402115181001caa58001d65074588440b802c0052401800c10700345441804000805e0b9a81c0e4400703404480e00840440c1742c24582581041c0c1910852841548070341c00840041417115009000d03101040c007071a901e2a11003000b40c4000e01d141010500c84c1c1d61510440f9070a1043c41c2d00d01c1200c0b01c082e103030f0905983d64950b00c501480003420050343c00501c660829070703071001755080002c0a041100030524012640c140000712100c200c0c40141c80a036480441c490041c001d140e0041c801940042c2a40fa20902d42001902c1c1c040d4075040142c03110030709a896451040c000e070056010360f811000024506a9180d08040d41c03169503a01211900e81d8003800e4600c402c0d000c4c07401280030900f18255441d444040c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 712636178 1250 712634928 712634939
    0x70f140102030702130e011103010503120906251515080601060c02090615070c084c021902241611161e05010e01050708070515011703040f 61
    0xd610003d60f01003284ca1b034800d140f05480c2c1e030034000e080318882c4010044d6680d50624042c1400e2240f504030041c80c12808015034111a201c01044030f000c111160034801024605c041c032035140348010340300a05403920019507603008200179030040d144000c00480c100203c5607100c1c000e607261042485644d000c507083d10324140c0035081080405600540050680c1c608550000c10307640140c100e120152800b08500d401481844010002c4441c085812003029000085140d035540683e403c102040070440c031b4003406207040801d41585103c0c24a0341450540d15202011140e00301c00001882e000014030841f499082076007401c2d102d03041c01700b24000078a4059a51104410048124200343d0b40c00c00100c0c00000d1a220024403404540c03012003c8003940a40c500603202240e11350304110070414188004040011ba80c014072a00070815003070808a450700c5607400c0119441c054030308054018050f040150040c82e190711402c1b41642c200c20310070082152059800c1307940e4083d0740261040705280d2007040c4030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 712637428 1250 712636178 712636189
    0xe010c0501020c03161a040b04060b041d03181c030e120109060609050a052a120115020601150905040209040e190309080d1403040606080f070f140102030702 69
    0x80450141002520305042c0c3c640d01861648490080804880045441c1041100b1b01210225000300c5811504040c10680c039140321004000c0c100400c0315030b45e040d400c0c120f900c940d0440c40000c10202021804100d2070100580c07654400328604080e480410b5210300c3c0d914010407060306519880340c1c80b00640803140d8060781c21a03030f00f481f820341c0295604035078035200b00240074184038280301d040302007566464528110151130000c0e01d140324890030070b002c02443c6841e80c03100454245081090320381850302040b410004e44214551481d407004180d0000c07407103068440092661608c0c550031100d50741e0b6203071542000f5290340d1540b003000035000030b803c010901e0540c01600190000420018000b050684498940740d030030b0b0000c050303049240c092001416000202c000080c00400043d180041014070000d0118075a80c0b60052802c00102c085402d000c510760100014084c0407085448030000f452460f652031501b0710a074a1510800030300400c245080440e507081e0888180c00544c20500290700700308 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 712638678 1250 712637428 712637447
    0x909020313122c010905060f1306030e0a030806040b0d110f0f130506060409020301080f0c0f03070614120f2d0c0c0f071502010609020301120201120e0a0812060906010e01 75
    0x130704000a1103000b02c1c0a60390305c0014118000001c64807a41c4031010080008480d03900c0e80f01d442450720304540300361480400b0802e00141a03040c80c000d030150351000c002400400607115000e400000e005c0d4100100185190f40704031041c411240402e2481ca400d0400c030020201489040c3c000660b00752104800c5a15000542c00400c02420a030a154681c1c0414040303030000d901c5102507500006050500e01c00a01a40307001c080e0a580c4801e081d48200301182c1d4900b100e202d41410883e4003c0795502031120f00040e140d00c0e10901000d2252401e01c260b261320266003c7e0742d48160142202210300034100150599840c00040a107090744030303541c003009000f1030b0700140e40c00441400f40b003001200003c1c4c01c0c45941c014005004c0103510002400d2002400c4600035040840c03114810001400701520a40031084480e80c2440d003a4460b101d1fa1102c00058444bc0c002d10702c40d8400c0d1070030034003000030800141c10007030099a007802c0c1d159100010049802007d40d80b50b408102c0081c01515594401d90441d13 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 712639928 1250 712638678 712638767
    0x12010618050402041406150901050903010903030b09010b04050904021e03060420040501080712140601090228140d0e1506090108120d090201090902031312 68
    0x5106a654040c5114444040e9508092556101d0811007185042d2092001c00b00c0c002c00440f805103825400715844c1e814000e06029031001c00f1588042c01e80c850800c075006064060b00900c5410b0003850040c003e005d4115499114549140011603036600b280d05443c111003000f03000755040d464680900070100031601428080c032004040d140d09030b803801c0000300c0c02640f00f00c2c601d90301400c2d001307000002a8034a17112140f0490800340100003000300000e0340b009480401c0d00d90003029145280c00c8558600d1148042c401e03015590000031a8989079010341611580034001e170f9401e6040c040d5040305804144484c02c0410b022a00040744500703054040e05031402c0d8104002940d04524091030f280c603c900e80e901c00180c0c8508200304c0c250038541445030040150761700426241004803c0746050b40078140c45205d05983c1d4801d400156031040b0040d1009003030582c011035890070042c40341903028980d07100580d943d050303a444c0c0751912441000c4a401d88036520150b0024881c82c0c00c9910f4900d0840c0c14103 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 712641178 1250 712639928 712639931
    0x3030708180f12060906090d080f0c090d0b070320031302060f070b060f0d170a02070e0702010209041d150613060608070305070c020901290310030c051504051201 71
    0x6074149038940c00521000c10f00107100600082c98078001c1c2d01c0c1b4240008084403408d42013003488258154002c40e0a6400111000c054049035444008440c028059090300070340c080c400f9411807083c000d085051034055001c03a9010300c41070141103803080703410034400c3d07890100d5041040028850f6100c0c3e513400c1c3e0780c00e100400c00744c078099502132001b49036040802d05840c040c0a200610420313152000c8010220a01610301044000c1c1540790340078918400c480500306200300045038120f00382b09102c11805804540404002030401c2030000303000f9000440303003d000c1d40c0703044190502010790071107503c041d14400d0014a140c00300f1a105403440f00d13001e403d00e5004414054999401a1a40103607000740c14255524586850303c1c1d00c0040c1540c201030501001e1202c101c856801680325900c28605480c0681c5906421290950100e1080340103101a1004024040103100c04805100401e0049a0042d05010b40c9142c582c1c0c100401f0340e400b4142c18500d02410801000716040c03013048051100c507120b00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 712642428 1250 712641178 712641199
    0x30f03060503070f1e260f031201060807030e1b0d05010c0201140c070215161212200a030c11160509131109181e06060303070818 57
    0x4a0300d07024a98200702a81e511000c400e000200b1801e82c41c0b0300d84010a00184081451b008040007841a141c407602424007005405001804082041d180d8001c0c1e05000ca9580d0007810b49819400340c800e00641c400100d5000109441e544a40201205d4100b45006040801c61740c044619900c001d028040760060f41c079803003030008101c01b886420704000f01c130303000441d05007210411440c0c9003030003c09144d0160414032060000d41c607000c01c011080722607140314564401041c650300d900d034841004010080c600d00480080c0301c0d80c0c0251b40500390130705411b040c00140318410101030141c40d03e094450000205000d0822014425008010f0b4054581001811a03242105031030412030140003046c00c0e8100481c00300502e0400410f003551048200518500c1988076507100b101443c034203501c1a101e02901404038074910b82c0c10f1660907920340141e04490254203a0080010800c400c2894204107001300c0b0001703841400d0100444a9041c2e0001b4030900d8a03e102010070686440d614045402150769030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 712643678 1250 712642428 712642439
    0x10905060a0906170d230304060b130e0123040213140702010b010f0f02031b010b0a081c0305010806011503020d020a0e1e0f0d1e0803010f061704030f0306 68
    0x46900040d001c003000801500541d02a414a1700b203080c04803504110442d100c1800d1100b60740c0c00c031a40e0380c3e0707420302e507560b6516641000e8000c2e03c1103101c1c25900c40c5096142802c010640e901c00010224828020300481c803a034042147c441c0c100136200345104005500280051034407401241c50004076220000da1848480001280200200c6d20340c0d0241c1c6d581c48000a180d03800c144900505c103098503040c0e030441d0103903000945a00454144070514110000c9012a083c002e400841e803000d0050151801242c0d100c1400b40d03200c20001ca40a40c5226a064580000f0710038010305068840c140000c180e242d1070002c1c1c640c005d01980000300c042690a0150080c87c08143c0000d20300000644e0340c036805e010b130107800c1007002007024281499070081031368004a00c0d110b001040e0380c0541c08903035504840c007a606103200c01480001004028480b4080da500c2003154002c080d40c16144428640c880e040c1e2201c600350790328065902d403254200715080c0050002445030007510301c900340701c2c5070201d880c56555 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 712644928 1250 712643678 712643681
    0x1b09130f0f02070c06080f010b0d0203100e0c04030308090607081305010b0907090608090d0e0112151e080601060509060702012f010b04110d0e07230906030114010905060a09 76
    0x2d102c111460b540845080185c241e1080d201d94000e004510302d54055450081a1003c510580c41c1440c0500d40100c001400310741c060407000010026504903c1e42c62610142092259100e40000c0780030074403d40100340300440c0012140d1240c442621007240c41c1e00e40c1c40c41d0341d1841c01882021156507403958006d007541d854404146000d0321907038486d80980740c24010007614a84000300510303000d5129400203210700d42c0c03089080305108800e0a00d400300d0040d11840101030403112240c2181204a0741000412658030f84003d03040140c0c204510303960315290541252035000a00c50840041c50500c00c416051070118001c00c1203030310505000c001e040e9200d05d4806203003240b0305255041c6008140e100c007014804e02039902c58140464041040d0303140424400d01d076000d941480c280d0640d440a0300e502400040280764060305000d01020380750324a0700d00880105044103c69070041440704003140060505020b48000003064003544500303a13090401580c0181701c01400c640d4804c4062100044140c0c89 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 712646178 1250 712644928 712644937
    0x25020c06041e031202210c060601050f21100501020604030806011b0b1312030b0102060f091509010603020301150b0d05060114180a080f070e07090315051b09130f0f02 73
    0x1a070300a805581008440010340180f509000b001c80c140400032084090008230302691f1009007420300ca40c40704001407080c143d0b405072694002d2201540c944420542603600d05861050100c2a4980d240a03218801242c8421043d00c006000c581c0800200304250300036031001c1c2e03081d01d910f148418516050348540c19180307000d44a15801e41059a241030900c8040c691603035144110b418244403852000c00002c0d55844001d03ca2414401210003080c149e510a1040700301183c02010b01c54040d05044e03407440e00a00540c1b004a03c658682495030b040342c20b0301c0c0000b40880341c1040b44181007260351130040e00581002044079041104490070b00300300c0c098090180c403d82d40007202402c06001c17284140541001c4540049105170b005600c0300c41080400a42241a20a080080e004e207844501d020f03503030540d494000416210000d503144c0301140c0140d100c0c921610700a6107040258074886511045031055425160300040307031001075a1601900d402c6142041c030780450014102c0315245100c4100c0e0032 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 712647428 1250 712646178 712646213
    0x70f0606120201080c0a0f0324030b18010614010320130e060a080d0507030c0c060305160806010e1c080c0a2a14010507060525020c06041e03 62
    0x9104160041d075134800b040540c40716441041615142c0790790005010156001300b00010180c03542a5640a20000880080700703220b40380500340c0191b2245014240701c10101c42c504030748030920b07400c030020440502619003120100d29036020000e11080c0114094401c074441461241a011003607070f00e51010724000c28401e0074207002440e2080c2045812058480c0140c1114484d1035521018480c40d10080b034100304203111410215915911703450180c40083c0d541340060310400c800c10300010346a4150304028071484580510030f40c55004100241c41a2001b81e420900040d00d91f403480d40542040c80c00510a807000142013424040315550b1010f06a000d000048202c0e003000c0c50210804c004d038010030003a5020490b05102048252a40032030340000391042045042d000c4a0341c14041e400782040301c040716040002400a4a0441e111205621a00c00d1610300c01030f0030074801440758030101e10312485150050485142c40d02e445d404802e42d804160031002c8bd920000400030000350512014141e869 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 712648678 1250 712647428 712647449
    0xb041a0f0117010905030d0b0a0e0c070c080d020a02100e03030408011b08130f02210d14131403030c0a060b03010b0114030601031a130e0606010309080d02070f0606 72
    0x41c1042d000194500ea410b50240c01c9038101340041c0c0c0018008416141c5900c40c01c00c0c002203100d868000a04a0045035100341d45040080c010320400ba9000b030010b1034024000c0c940d007a42d4903580e021082d5100c4100801200613000701e80d181c0700615150300e549280c10610300d0000c0754070341e1b0003000a0541c0d0040d0301003186a990303165404690600c0407802141034407142480482442e00801040940c56881c000409040360007034070400715034400e4030100d100010250141c09002c03d840f50b00f65505117441eaa680031410704208031544025000c2211052001c508980115918200082c001000001181d5915010900030212428810032062040b80d00076a404202058120141400c41d1138240040b41000310001107040c104200404880e00101c0a1a000600cbe00900d0108074134041c04007a69a40f013145402601c01d071701283e803c00f0340300c9503042d81030300c0403500e58000640486066450080083c402880f1451980c4559409442c00380e000e16500c001c20031103640ea207422122140c00000201 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 712649928 1250 712648678 712648681
    0xc0f060617030c15070f03021c0501030f170c0309010518060f1e1303020105090301061a120108010504030e1009080a141902220609020d06030b0a05060d0b041a0f 71
    0x280c04021103944d28403103000c0c81c1c0c51401c15440c000d180000d0041000241500040c1d208a03d10035010300d028001c00c0c41500308610f503128a03084808140565080c0e03040d41c81d03412002c10160b085011180c0b05805040114500400302d40159030035040141c0180d0401d09400f13024145441e00c10040110301e112801050b80c0c1c000310400c0c860031010044584108007418008003d40d003103280144000c2d00e03024280715403603807540380009000d00a01c0d04a21030010310b46001c10f0303070f00c088034010f0900b200e00800e840f5000d81e03c0310305980c00c0f24400c943c0900042c40c00a400105400c10711082004440980b4090203903580795410035107445e00d0290304548490800642d14813030402480105801a140f0203002212000c60b000580718012405c0314007650f141381040a003061515a0042c0b0040822030000d54580b0040c4090710000d064512007642c16060160001d10f903400c091041742d00c5044000c00346603625240786c6600c2c90150005004032a02c10030b100c52981c40e01140000d45110704d2003018889030a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 712651178 1250 712649928 712649947
    0x12030d051e090f070b0333030d0201021e0306180c1201080a0f030e0f0d0503090f060705030f0d0b181b0a14030a0b0618040b060306010c0f06061703 65
    0x8107801403000c04203070040b403d10140d01e000400d92400712609500d5080d1680c8407000181e042100300038000103071102211900c1c03145082d04000c491005821015911107500c11042079003130744608030000803009400d981003940c2c010ba04000e1a0010405004807034088503140c0c00110f81503058840ca00008400308092602c00146541c0a0141132000042c0420700c2041d03658082c030300398044004090100c8501640741540300c18102481008004100381038030280b0b4207001e6240d520200205004030380044406074103043c2441200e03805903010780190320b080c905c09002c18144d0800d4505001286d155105110140e551109180c2030f2490301442d240c941c00c081c682826000d014907002c1d03005000622108030002d40242c0d4507622201d00c0f00c10160380c4e9440300780c024010808a508558030030700c0410750b80f50350104034501400c4040c1c240d400b00030103010002048014001160100e002503001c0e00d003c80021107544c0011403040c810380c1c0100d812510340403514245000d800290f22540e1002c69035184 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 712652428 1250 712651178 712651231
    0xf0a031506050901050307120b22060e060310050a02040302130203164b0f02190c0306020912010e21090f0105071b0909050d030e030912030d05 63
    0x520250404030f1810100c800040c01600008090b903041c4034040c050b200c0c803444035400c030681480b0000c040b0136801841007807503942c01e151801c01008180c9484400b080c1000c00001e03c40c001c140084c0108280c00140f1103243c0a030500800407850550207010000058940f403013120b81c07000050b4000361300c1c2d01d0990464440d9100880d03c2c1d0080020440281d41204040030304004409003001040c0c80903c1202201e500fa9854443c042c5002d040b0b030003400c81040d42c44280e030300762020f055080e1001c0c541c90858503000010607481c0600341050a03102080003842c0c1d40d0060110301d80150001c16480e00381c05002e42100c0403011040301540144142412800009502d041d6200f2007810b10b50403c002c84c404180c01c070f1800c1c0e002038144200041c038101800344115017220000c1c0d9400444646030b4403072a8600c040d1175040001c0700d95200f03190600203054064004c0b89181c000d08002141040002020040a07003a000c0280341203010030810440344801e01d004dc203100324103c103413900030309650558034070 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 712653678 1250 712652428 712652471
    0x106180209031b0f04091e050a020a0f030308161107030c0501020d03062301050d02042303150a020904020c1203071112070b0705040e070e0109080f0709020c01020f0a03 74
    0x11500d81028481c0f410640e100c5081e016446826100000c0031060392030184407050710350309103a8a40c81d20a50303050822000080c00060507201307446c2803400707540d9032184111007150303804010702042040d030005010180390f0035011074907103643c0341c07240386040101512030038400c1c0358000761031800c4440000e00403560100103016920b02903103410098285410110401a500c02c988101134800410726040755038850020346140b1980c4c6c0d41c00b1035880c1da441d16444452001d020380900b00c46e44440050034281b801207804112410350540100760350303a4402d10b2000035804444e042c0d5100f5030a00c8a21040350003000b03180300e845030b840d015503528200640d01804410365142d000031176500c21600241000640707410f60f001203500500310042c945070082c2c140c0b0740d07001d1740d04a06030741c2e07100004000d1525800841c0d100d2488082c1c84014817661680ca400307031180106800c0d41034581c401035003000341480f51b034014200e12302c506000605209040c44120303010b901403d00800040c1e110105001100000d0f05040b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 712654928 1250 712653678 712653703
    0x1b020d0302161a07021c0c0803030618060108040308061507050705120a200103110a03090b0609090a1b0e0702060109150302011205100e090f1911060c010618020903 72
    0x200120085103d12420500c10050001c0c015041645000c111748240b08040d131000703a0103801c0c841d1860b291000c143d600e0700b041350014420109100601082580411014012031040c2e40d2041c182c0d4507900c09681e0f0b054064031054200941000140300300c403032407000d041c8440c418000b62200780e02d001e082190540d401a10720089804c9104504000340020418000c00e0380e44144076425120b004006900030f000405100452003400a10020b104e6031650100008520030034040010340c445006118140304104c80700041170780100c04100105400b0064011501c544041111029445410101a0440c1a154400580e2000c0010f200e0600300f4040d170540000c0e50083c0c404418550340000700b480d505411000c100995a90119003516100c145d07910240484020b03035a0305041074a19a991004078030862034813402800410008800043d003c1003001c4c0d000300002520041d18810080f40760b1214084090541d6a05000112800000364025890480580046c0c031080e11005043c204000003002 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 712656178 1250 712654928 712654949
    0x703080117061f0b0f0415030b0901090908070c17060a020708120403121b0e040506030c01110f011b0f020f100b0102030903030d02030a0e1c1b020d030216 68
    0x20040c001e0400124954811070103100100d00c1c18400f60180390014064000c00c400b0540015042034400a00000740304450441e414003c81050b40002281160011000c2c1c5a004a07440c0c01041003000941003210740600400111f480e1035000e568903100e05100d684600060500d089004180e06024400141d114820300c509500c0c02e081c3c1c0e91003806501c1744201c03450401401070042002d040c030400448070040c1c001d0b8010007202490400c10441e14221040e0f01c0c00244941483d00f0403030605000350390080d21f01900414024011000546003003041640c4600c8501c02d42a902c483c04900340202034040b1400140d052102e51a108014107c0300c1301c1c0d1020b01503612416035400101310001d00c548801060035800610719800c200102d003107105071648580e2521010039000d034a003c181e4005c500600c00420104801c400c0041c0d1651118003900c148281da80700c5900950409004030802e507400c2d10204020021a040c42d40020914002c0000940069000810900c0c010b03005480d9000a401c07a40403 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 712657428 1250 712656178 712656209
    0x31d0423091f0c090e101e091406040e070501140f2109012a1101200301051009030305030c250b06040b120316081317010605010509010504090b010c0203010f0207030801 74
    0x7035488044845211f104c01600003000c4004070a4a000c2d00800588441031061000c044001040082c0103011f0320410711641c50950610380f0000006110b5007200c0b0181c5031a1400d000c81e2500c8984c1d60041d000081c070484080040b0180b5006211002000f0074907600c0d20142410009803460031120b8a01c114995405541c45041100519a0030b004920917030f8549078a88140000c02c041c0540030041c50351040042e0250b00282da50001000756040c0c40007514003440c4c480700d90404803056240b900c03015001c6441000440d1814050600a1101c810324141c1c030105030750031909140a002011000340d4039841e00e54140025071811307020301850b00c0300495440307044001001409440e8880d41c01c40142d80ba00301c10450003000b109038240e8810229000c124215642c1c0c0709200c007080e26904c208481207502e01480418158055130030381c1c20055040e544c0301d0a003800c000c180001030600110190500502c1c6103041c0050780d0074041d0001c100c00503003000d80c85901506e4081c20030314040c0c0241e40d10022124 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 712658678 1250 712657428 712657441
    0x1020c0a050c04050f0c030402040b0a0603060503160605030c070309051e120708030901031505190314030c062805041b051e09041a04031d0423091f0c090e 68
    0x624540c1c2085075a10f007503079aa08c5a02c00500100504040160071141164001602c543c01d5800b10084030001e0b429100541c6000d10381008000540c0252800702e802400810f140700d83d114054880f440c460b0a1044803241c80d00d00003040101c00140c04a14038a5014040600b800c0034240c00382c0510035040101040d50410140c0c0c1d07180c1c068003510301e0404d9540d01c03070b1148a940064904d80103120190450b1956620900c90b61140185404265007804185011030080040041243c201a5161002d03002c03588900d0984802c9100207002500c0e501891400301100c01e4451140d01d004921a042d407044d5150b102440c001d03200c55580c025440395103581380d103a001201c104100c0385000340840b48201141e81d42d00e880c40c201100e05600440a0f036030041040201900702007448410f880201144c00503891202c10081512840c075030120f01c2a43c20400d800100710681a0150000355110a5500044846403080b41c00d48592130034490040c4c403030100003c03a6402501c0e000140511805182c010314149 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 712659928 1250 712658678 712658701
    0x30f0d051603090c211e06180c0513021207020a050709230c0c0601150e0f180a1e060317210c0913050f01140312030606090301020c0a050c0405 63
    0x344102c000f20042030350340c02c164004c029083c170038144d413220580a20b001a1800307207a00c020b2000080f582d0904e0104e84800031107401081d0708460382c0c408180c403001ca0401c024001c2c0b0380c840d6042c0c4907006809001d000302c500a0440f4451162017541c1c002c1c0004c1d900b500b01585820107507802a00783d14a060700c2e0021222101d90408a1003030035508940703054840c0d00c40c0c5849440390030059242401140d001098030b20351640c0c0c2880048460360b070030003240804420441c900c690a446190b0008402044024102e034250016910104032500029120b4402402c0008030f000b00d0000b40c240c40d5210014000c1041a036019486044485080b03401c03c1015a020314001007417400d0072520310302c8040003c454160f00360844480c110040d280130100b0810800c004064003050703403c4949402142d0000c580c07000300540500c401000107004095036840c221194010780e0025004581003501000300701d0705510709000802c0b6a0b03030f90100601c103c1c24203080240c03c0c15031503400148910b0900061100351003c2 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 712661178 1250 712659928 712659953
    0xf10020c0d0c0f0f0e150a050909010b040612031d0a03170c030a0305091b090a0c0e0d05030406090b0309100f15030b07030e0c030709090302030f0d05160309 69
    0x41d0703140c4140042500305403180d9403055009000502e65100c020450b00549030f40748003100c10404629540343c0f0f032403220342c01800740120241d4000b02030100800c01c61500c40c1d4000c3c0c01262040000030800da0460114082d40c245410500410300310344404400c00d68450000c04034080402c01c090070703800c41c2c1c03000262400c100f44405844041098001005040c0c074604852503002020200ca9498080c060064042d0000300c50030a698000ca50861000300d001c22450100d140d0004c00d04149907480c080c812004003140f0407400704101081580d00342c503450b100c02c4000f05a018200540d1102d02e0024001c0441034140c020b8503003004d0074410301102d60400202088400004440400c2c0301508540c040b00600c0c41422019214400d0f1500005101411030081d0041100f42d0f42403000200080c0a0703a03a488001c02900c0d050780c0040010000b0030b0303082d4070550909210b481541c1c6050001e14900415422061901c03480c0c5a43d4014480a01e00c41c980e143d0603801581030601000c00192500e480c4404d6 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 712662428 1250 712661178 712661203
    0x20307050d200303010608241012060305030c0a02030c010207080c010305041a04031211130504091106030c03070e1c0b07140c01020c0d03110d0f0207120e0f1002 71
    0x10040126516500420042c40220541c2c60490707440350b0b50b8510040c401d1005a92558454403841c00ca00e07240300001e03c03004261240508080e4441c802001e04468400ba40340007007000340e43e607040c04030002e001403005083c202d01b0340c8020000c1115900405040090020440b0305543c040c030760400c0301c680045101e07035107040b0900b00044c9598481c00c209491801000406503a29103107800c001c101504040d444242d2029510304204da000d942141100074410009850726020340c80100b040285026004041c1c010310410100070072041c048049034650300140c401c40c80040d0088100b10605134410041040100200c40351f1682050b0034028018104160300081c142c01c40c0320000408030b41c025074402280659075484603039110002502c041c003d42058000c00c0443c020124940800d5120b405840100710420a043c0e03e03040d02000205c000304000c0819048803074082c000032000c2202d42c104420307400000e40301c0c03400e0418a04200034220219900c0d45106410381c85003103ca9a9000031004100749 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 712663678 1250 712662428 712662437
    0x110d11040f0b0a0c06110307080906010f12081219050f010e06120c060324060406020d05070c030b010906030204050f0c0d0e0a0b0a060620031206041803050a0f020307050d 75
    0xc81103c0458a030701062070050807060a19010001241558004501c42e850640d10340c0b0b007540b40d0341142170b01c2c0e51083c4103031035040401e12000c3c0b1a06404030442c04100388503400c001d140082c500c10016650808076a00004010180702860541d0001d000d0558040860b0007a45000e41c102210074803507000c0a49014091302c0e00d110100c500b20020005220300d400000e0010f502e03450502488170516039030380e4034920484d842c0100044542000004da40031764005802030710414115030300403038040d000001c05560041002800201040007001018040c20190101107051811401030005444e4051b01c035032000601001080382040c4a4401c1d83c20b901481d58000c10b0301020210f40c039182000b0901c020300403400c100c0601401066aa102d10b041350200e0311a00035904110f000e00a040940c6039146240c2d4104108144108101010780740e48003030b0041000031040c42d81c040c1c000700e64103215002c40c046000000c40417801608043c8110b815981880198030341500b56a6090325170741e48254440c10b01 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 712664928 1250 712663678 712663687
    0x50309151e150d0809040f1404080f16110103110a0c1101020721060506090907091e0c0e0a12051c0c0b3c070e0112110d11040f0b 57
    0xc8040250522110030000c156003500f0750750b403c0c68010b56020741c07805803149150500000d9102c5490081004244502318031158640e1071340c40b10206503011400e414251001041200c0800502e0a92812014094071008403a070700144000350072150f036068031200f84c8109200d070f0407500703500035003801040b580500040c2d0b07804601c0340140d16007120340d044035400c9030340c2d5401403d0004031a049400e480e401840c7c10710094072240d040c8510700700c09507005940340d00084000c0c080640142c101006030409032a980121b000004030050440f07034040c0d950380c002002c40d10b8002e000e01d4241c1c1c40c04060414440341107c050060344d00c95684a50041d070b16144214994505000c250260442c5088290440000364030391505000c01c1780f208060b20804030109401d05000303181c00364204003464440c0340d04682266540c994900543d0380c540b544e0311040c1040355252420500190790700600c400f010500a083da250003a0082e581c0a0b2151650900d4807584144010407101c40c0080c01c150494010720251550b6 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 712666178 1250 712664928 712664941
    0xa06082a04051c120801080604030507050c0a0e0a0b1c150b0d211b0303050411030d050a0228030c2108091006030b01140a15050309151e 60
    0x300e00899011560190302005020420054920110b15091040844c462051004a401e0303500c10303c02e00030784170150f01c81c90028000034082c800038911a4040c01c11121609008000601040e64540107040c140c03080f48240815031001d4020354010300e9003100e41002542049905400300628a440a04110480f400300c0100c100c841c1d210044c190009441d0104c9003d190400c5100b9a01c244214545400c0c00e11107404003600c0307907010080b030f031342400e04141200b8056201203001c2c282c068802e07500101d0b0702d00500c0301903408006809040c105529401d0700d0382c40f8080c01a08119410540103150407400c0310219001c98441c030040740542c2c0c181004410804a418610301159440c008001c100001c600486522a0000c110038850103207041110059900b498484054450900c0000d141089140060022030141c1542c00250400a04090885030f560301c200c0820903d029444c10204500009000404c402405a40340d0070980300d100a2072420041164150740070004ea00ea24a2106000490746 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 712667428 1250 712666178 712666261
    0x90302030306150913020403021c0b0402040b010519030501170a0b01290c03040302090c130303050a1103210129030a021b010f18030203030408030603071a090a0608 72
    0x25100c0f130282c0031071803192101100c20000c0d8840d0205a10440442c0c8801c1c5c00e8040200c120705000b41c0c01400702405e034843d582404050000031200d14140030040c004465501750810314106c403400c1540c3c1c0444c042d49090810410355205a100400c03070740155850300702007410300149604658a030001148a003131409040f5190416000c8201c0c074265000030401c170360103000030183c0283c2c2d00803203d02440c0d8582840c00107451185041c0c2110b0301100700b50400c00f10f80a4805404110028204030a010402c01401415076000080e581c05209400800c00c800b00b200001681c050200341a180d454501c03052110401a4860b83c00c0e02034620b0000b000584805550b0142c0e0207070840445901d03508034120148074080c00949072108561031800d0072080c420b0148144010001d0f8054010f10703d55140c50700c0b000c2240d807005040035018412a0350000700b42e016149800301c10308084202ca83c071200c420b42000340c2c03212207034001c904204445051242d03000d4103e90201c0d4014010788421480822080a083c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 712668678 1250 712667428 712667437
    0x503151507050a0507050a0303020d0e0f0604092906040306090812040812090712030813020901030b0a050a0207021e010306090c020d0908010501030809120c030d2109030203030615 79
    0x90032000700d000301c02c02100003038005403070784500c0076952202d441b0340a10104c00d1b0b55210240040e803103a480582e0141c012003040946440c0a041c25a19a40310300c0461002d922550210301709a41d102003604040f14902d071103d80341e443d1800200c0051007010700066031805140400b400e00c56940c4006000c0211002c00c980c031005c1c8404040d241442c00b030502080903005001807582e4042081300007900d0700004107085003542c1c0041d040700c0400c2c010382c6007110030b1900200102090080000f502c005a500c00c031311140210300c5886500b03440d1500d12120415580e02502d02107005005100e180300503030346c0745040c40743c4a07006191440d04210703400049024003010b90155210b64500407900d551151b01280700e00352038403143c88803d0000d964031000ca00f226405d200c0540924000c1c000003400307107081007107030403130640820071181301c14200307800a82021000c0050002048032145051800390840ca0080803119444504114404540c0c802035280e103c001c004d1440f8860281d800c160000c103110a48 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 712669928 1250 712668678 712668709
    0x21317070515030f0709180218030a0b011a0c0a11210c03160e0c03090a060c050913020a0c020f03030d060305070905330414040b0a0f0b01050315 64
    0x755000c00b004004406601c140c802010350003041000072440ca000e10281401c0390b82c0050207040216480702c0910003900300c1e01c0116a003030f05104007503041e960100b16901626001c1c0003a802c0c254581500003075003064a043c07101c0c41c1c800034409810101d9002c15400c05c0b80740c03c00541e1141d0002400003d141c00c4c84900011510b80700c16490010541d0001856494060141d00f11084402e180c0c40b181e0700480b0504c2807908145d41c210004003c0008440503507082500442110000c0340142e0b02e01c010f40e000b46100400050021468000f03518042c2411044402c10801c11440d019a03080003c01c20050300002900031500c1c90400c103a640c40c00c104403942820102410000141c691402c1600e604407032042e4900e80c0d041c400407030504000c0a03a0510301400d00180350140019419a840c4482501040e4560050f07552007071041d81c1c120480d0f25803150b407185400c480503180041602c822241a81000c104440c070b000c04003110b9981000850750030032250030503400100480da0008010701d04207001c8 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 712671178 1250 712669928 712669939
    0x709240e19140a0606030e1c02030c0f061f290f0c0a060b040b1e0409080a08041208010f050105131a0c01051609090221070c05100213170705 62
    0x610354810501071665010f45902c0b001405060341e0361208034151410680d031404150071010341c00400c46030107030003001c00902d02c0c0192402e00720355500781c03800c268169003541c40b0b80d0045010030940703a500c100030300f10300c0901ca030f80040314034100072600261228641180e0001003281c111408020320030360580e5101c80500d8031266030f540d070004244e5140d00300040220340140c01d0401d202d12603e00340c010310210b03001c00382441703c081444511403d0341e0540100e42d140c002e07a9404440011540c4040101804000c03911001424109450300c0ca14200804c4a400104240ca10050103181c60680148084a409290894071035002c10310081099441d5030002215030002d11005940e400c03031101034042218130038004c011560300c01803c00030582e500c030000d200183c80b4482c1030100c10a02e030b008e001d802015000c0328030701034400700d4a11040901940e070a80441c1c1c0055031001000810000030b0701c04061100158100f2400444521990b041c50007684080011035000e002407000c104586001400001c14 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 712672428 1250 712671178 712671191
    0x9012d09060f05030613170f0c0114060907170a0906060b040801150b040f06080a020903121902031e0903160902091003050402010c110a12050709240e19 67
    0x82c8582000541c0c401c080c003078029000081e8003001c01ca860568010b40045d030701d800200014916071714650000111400d001820700c079042951009200d50741e04c3c0c0b2104824241281818001c00c6003200000b00001c0c10441e2605401e41409403044d141030700074509403070101744c0b005946403440c007800740384d0090f684455001c1000680e0a40c15001002291560500317002900d0b180c0b607105c0b0681c4a2800343c1610881d11020030410b00d846105e040780c1c8035004000050400030504c00084c01d045080008061310075020070107403548041c400000c00d407546035000641c03030042144007042c01540c50100e030b040002d10210304c00301f083e102480780c1c3c60302082000d00555020346890740e01000350401c41440d8003500501d0b0032004424001d1040d0742c01907405844010101034141d48851464110300815500305101d07480002c0c2903085412100c2c501803140c000b5042c3c0c1d0b400d02c0c48050440700e4054002c07402585100840e0603001d14181c00360280c45030382c00756610568070928240c06c01000640d0403501c881c50150b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 712673678 1250 712672428 712672439
    0x219050606010306051021090203150115030c0917010e0304170705060301231309081b0106030b0109050703020405150c0c15040905180a0503030403030b09012d0906 72
    0x110188075007001d8a00308081078403403040c0000c030030f2003c1c4440042000303608404003181810030b4182e51907443d408007094182090f4042420a41c000d60b5200340c07540d07180014450103e4494007040204101c0c501041940e200000007842045984110403205246003800d4800c1c240039042280481c041c80d0480e90b4841d5603507510344294002c85070140300784c0200b400c0440c0d2450110300b205d040f6500c004000030340000c00700c85a440d0f8403000200b20740c4160001c0c24052050a140681e2014502410003581c49a0f12812813088640803092101400d03490854207100251100031618155098410005441e0f0f0f585482a40244641d4000e654420a0a84002c0d000c0566500410141184505031281061601e0910000c0300d009440800301e50824482481461600c2d4841540100c4a022101810b075840c1c0301d940c20101102c00a94203504008108414507070540642458058113440022007589400350340761080000023003045c44440360040b05903034400115118406003c41e1041000b240b40e54a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 712674928 1250 712673678 712673683
    0x60e060906070e0d0804090f1b090f050321130f030f03030f1a06091807030912091d06120609060714130e04030203280e101e021905 58
    0x4030380b00b00014221a55140540c14034801900c08154410a05424541031028020191904100ca00505035a4800640c6081c0010414607400100c588600c18042e080801c20f000600b42908464020340c0040140304002c08050440090390052000058071100d48101f00c0c0c594140701d42c802d2110b03881c403400120600400d440d145064501c00e4804000d0070031200780d4002902d041d044400c04a81a0b20b076100d00d1410400014050000000c0c415141004620305002080b00180c9421001075640c0c1034a0302045400d00903480a1505401c1c1920b4451802d48110440604015441d10324040400071911649450040b0041c403581c174000d070303945480c11613400d076034403c0308076002000242540b150078078003410300c170032241c0742917550034002141ca04010f4458603c8601130011411032000300320110030000e02000700041d41c0b4007a428004140c2042000500020007070302c03860310500f021150541400e812100c080303540300041d0018003a04040b01800c0c0d040c00401441041c0004410f01c6a80401102 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 712676178 1250 712674928 712674931
    0x1504030b1501080a200d0603061802012006071803230c010309150c17130b280e0709020a031407050412150b061215010e0307050409060e060906 63
    0x280e8a50041da034070481c105040d643c503044805101e102c40248070b0408852240101075094a1b1040800e2150703881d55072030121102680c203a44c641b4040d0315200f0441da13012203200007118040c070705540700400002072140c58000160002052200c01030b4545403180c01500b04c603000b190400448403203840384881c130048031000b00c2d1036803003e8080d800c000c40482d03000b84a040300c95038110740408186490303007000f07400400d500f803121014450b110740003014115000c1600c92040c6204c61011540d03032860310300030303e244001902600b06818000c00252588040000d4100d407000001c101203110310000c11201d04182c5160031565559000003603a404094054000c0c904010700c0c5040710f8441d59501d0400c5400b4082c5010b20314910508007003a001040341c00c40d840c10114074541c0009240065080050000c4c2d220420301590b0b10306440802141088500305080480030a003001c6800504031400681c441c40d80c1d0040130311441d500d409800030300400744d02100510000c01c044a65a0901080340c9030384000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 712677428 1250 712676178 712676221
    0x312050a060b0403030309140a0320120d02070c0504020d0608101a09071b060603030206070207062015090f07080a0c0302103018111504030b 62
    0x20040400c040414600c14602100e103400c0d90581450b0850790304401a01d04c210040e5450f190000c2c0249826100b8490200c525100c3d440e50542e100b03000300480d9590a00c0e11803694030f9081004d51100305041403040358403c003049140180e41d4007007031030f04200e070b43c00c0c50300144d41051021400541c0300b0507a5210400b9682440200c808210303143c0c00380820369150001e0302e29007074540e1508043d682003903200d40e5045540c90a0540345882011050103c48956150036681caa4681e4001c2080c16014041c141c0c10200768409051403c0c108400a000d41803e0403940702e1300f904020003d503000d002440035100d00b0b05000001402405c0541d1a03c1da2480400300b6440036010f21000094000000580030030155482440101e10364619005c000e500c201000c0c1032800c0c820b00100b00d01d0812203880342c0c044002d030401e0b0b65942501d0301e00007400440310300080300381111100c01c060f0404617130703020010303501c05c18101d402307001d0b0141014112445004980c4001e2414415006000040c021444103074a07884 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 712678678 1250 712677428 712677431
    0x6090b010e0d150b0a0306021602040605100816020c040216020306090316060c090e2a090108041202031b24010e0402010f0224060a0506040b1c060308070312 69
    0x56058042101c0711030008401441614401503e04419420303421050441c50010100c4000540d241c451030f00360f03442000c0c1003c00500551001c8110704c1c00740300c0c0c400034010a0351001e5800000c2c00c000307005410040c0070101e481e03900c8a14040414820054401c6e40c400240040d511901e1114174000d07d52501d541c00c80c461301039000058810540001a40c084500030560307001d04540e2601c5a030018001c4610361030030003e0010f000314480074840c0c41103001c1c440114880703482d44440000c01100c2c100c03413101c41c0500941000039004681c0d02c414402c0e00b054210b55695016460321800380d245104000c1440001c84045044000f50300000c55000030030840780741417061079400640700c095540c9090040d030941403080b01c007003405035100e4840007a0050050046510810041c0d00d040740320103050f03a000305001044030412000c1d00b80119040000e04003542c00e2420117041c001c204440b8054003001100e009800380552110324030540052004542110b0501e590306402d050003088440700d15005010507 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 712679928 1250 712678678 712678697
    0xf1e05061614030106030b033f040501140d060e0708040c08010209100e210703020f030606010512040314071a070c05070605070318061119201306090b01 67
    0x160050b00c01440e0300d0038400b0224a1682444410740c024a9600ea0a9800d03100f4200c1104c9807651040c68415201000c41d04d0034940f90301000d01d00040d42d103801b850482024180804c00240c0d0300302030801a807613100001903071100c04038140c43d40140784607407041d00d182d07d40b1740034400c0c5d0a420840c5140150f0041c0610990240c0311400380d8281d02c207095003179030000860001601a644207050703141c919039000308684400301c602c40344129420310401100056801c0f900c02042140380c03208404086c1103058020b440180b0744140043c0150182ca0b01c810110400e40000408140c828400b1000d08480061516100c07420b605107403484401c030741c402003103101003000840d03c001d020b00001201c10703502a00070001541481d5044600340c010030011400d2090010380b021101121100843c0640038581e41d04502d0b8030700c0d1045500d440c1016000c1045048821b403100c2c003103001d0b10a0a0084064010b8003410480c060020407820714460080c90000c80c03508502044044444d0031215050324240d03201c1464 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 712681178 1250 712679928 712679971
    0x706090f02131802040f1805031903180816050d081506070b0109150b0d2721120212010e1f0e070c0209040503090a0f050105070f1e0506 60
    0x3c03564000802402655907000c030b2070042c6400d0700301d200e544209403008100c0768500e00c401c0740d46419801c01103030990000b040000040e030b1500b543c8d00011260b40f80c03d216020f030350045400d0b00e2406c000098a550000108004052000840038111300d83c0542112903010718510010b1243c4010350341c0d120640d2410b05014581d1910005413003405801007018011640303001d0502008016035106610701c10000c650011b03404007000c0c094424102d040c1e01c00320b8815055106a541c8040308a541c2001060070401000401c0b94444004107029a02e8000324a142c440441600d0b880b4010703c114960760300004e00b51050000403528141200d1b50000148d80617101c141980c4001c0c400320400010b00742c81c40808001c0190011040c41c0c02580f903083c04d420480158000c200404000c54082d200b0340e00005083e030141c00c1552845000b04820020003284500b07000000b40144142132000c0c1c911009841302c03005009071526003500cce50448040c030301010040c1740342041e102c60040319503210b00344a0061800e607 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 712682428 1250 712681178 712681181
    0xd090213200724060b071401060603020c103812010c0e090c040b030c030117070b070f410d0e0d03170a09050c010309110409080706090f0213 62
    0x720158000e00001045121a03070360b14001c81a0700e4040c6001c0d4507940c0c002829642d810050006074040c1f2000c212912150582d00c1c20340b442580600c1c101481088041d07140daa02203040b011803488102d0108010505010107416a04181010000c582c0b0340c1a1a481070303990426400d41700d0700c0a8801240d00180c060016081701c080c82c00400124000e0214010186481c81703545521065000300c039814981c0f01e00310388100e90801c0384e00b042908800001845502c583c1c1c0da095a203001c04d000140400c03400e0500c15505400b420b44000c040740c1c0381001c81c000300070102c3c918066140110078070410b00c11490b40403d00d007041e4455007507034050030814503c80c2c062011664411b07281c0d903602c40d0080c800c651800e04c0911140900103804101001e902a1643c04070b4029150250100b140045001d10242c01c0050805110601150600d468414072100090f00c110740d09035200c5080b2000100d24141e400c00c42294414120000c02c002e181040c40002c100a0f80c0b1b00e0900031303000f59203600701d8150610b000c50 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 712683678 1250 712682428 712682437
    0xe03060f06240c0a0b01150f050c0a0f0501061401080105100e1804050703120f091502070e010914180a08070c03140601090f18080d09021320 62
    0x69900302800040141c1425100e0050b40c42018086220040ba05181c1d80455003050a042c0c00396082015018140b10340900d005000d401c4d04602c456450700d400002030000308180003500103100000c035451002100070300491040ba5003200401c20070401c0381c81d10354020441402210762100c0c1014040d0105c1d441140014160b440c050f00c090308840c0450380c00d40c4d40e54060189298040741c5200300c0307281d18070101156170113588600000d24a40e800c61a113039030841c8a480c0071500300021182c440344c540340d00c00d40543c11618804d032040055600b0f084220b0a0920a800c01c1d4640c1843e14000588101254080503049400d030781603107901d031075605101e17480380d00c1d4011017075135903000c2d04070300000c103156400410ac41d43c825000c40041c140d0b650340d840c0001080140041e156000f0364010031220170240120b031494100d9800800101c1414680d048440c842d404001e0441c10b80400e02d83c05000c080c4e0f02894559400810a1070f00f800c074944c14102500810600e403005440c41740144c501c0c000000300382c4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 712684928 1250 712683678 712683691
    0x190909090201170c0427050a020f030f090f0d09091a060a0e0105091c050607230d0f02040f06170103031706030c0a09020909090d0e090a02090406150e0306 68
    0x1982d40e81c00768800003000c6601804005440c1d04c20003000070842107048142c80b0b1401c08a02c64404a048404100221400142503401083c0104003509482c80310b54100c80d4864140449403001d5290f00400510301030811242c40801d12800c50900b81c00d640264a04c011200030903000c1c40704102143c0201a1151002000754202c2402d00c04800018003450007844685010f1515a00b011400c40c0041e2840100345906490b950080c98442c042c40014803004c1e600c241c05040c00c3e041e101c0c808900c01c3c042c04c1d05011801c49410701040540840c01c3d00c4c1c002804001142070159241e039180c1d080007440d525180f01742c401150744204241425000000c00394100c0f900343d1200482d03003981c1c1c588100b400701e00900d050b6042c010280301981c25520700302c141002d028449401a240e0807407205100e8046809802d013400c076840394218000082c1e1040c00190304000a449040040d02d176070103208060300945141a42c01410010089000055403454183c8004907030787c0c840702d110341d410602d9150342c4140d820 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 712686178 1250 712684928 712684937
    0x507020f0d0317090f0715080a0b030c240307031b020607230c01060f090b0a080c010c0c0806161e140a02070801090b040b070203041215060506190909090201 69
    0x10354070300c2e0808120b05500c04164400c0e00d0209100b251428240600e940103201c040e03c50801100703550394403450550340110807071020806042b241c070000382d540010a000500c1200b0b8590000030743c00844650042d001203030960a80c50b4100321002a0140010f91182020f040030348100c0c03039005200113407540c01103116480703040c000c20380d212400009149800d40806405010005110764a0003442080001e01e041260100701c20309140801c41510462141c2c0d510800340c0e10001c2c0300d03074080451381c900c4881003420075004090203850164281d410a078000c0a03180120b80c10040d00c0344d031030f101120301102d6542d624056244200840d803146000495070f0700000b6450f01c2c2c034220101070030307008054403080b0b401210400c0d0740d01c503c0c86082d1050b8040c111140100d80e401d01041001c05000307143c0016090000c1c50619081c0a12100040c0305220003034610300e0b0170000e01c2c10f03040e45548084040c100c060071300780d555603030341c03001c4002c074040c0041e4600052250b00000526100da4420904c038260305a44 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 712687428 1250 712686178 712686197
    0xe040b0c13050f1f030b0415030b0a0504030c05030c010501090b040204060e0d140f0327100305060402040504021909050f010f050c16170f0106061b0f02100507020f0d03 74
    0x501c41c43c400c00c0740c03101e5046200740e100e10b1240307403103a480c0c81c443e480d0079907020460718078410500086c2d440118400409580021042c4000f07094854803d510440c000c4000400b9075442c1000c940c0720800c034a0150442c04009100c46d4404010340002d4140d496014042c0141c2c400d4070240404ca2065200c0d4200049a0024211161034186210580d4601407002804661a540403042c00d240f0840840b4107039500000b0200050b4100e0344062074070390300c18110300c8040c0800c1070104484219881d211000c05655400140d000c2d6215811303100940400f600c115121140c071542441c100c000381201c0380c0400c100d0700002039245042034a15520303180c10ba44204d0301c96214202907031307190000c11000b14980a06000d224180109240c0c900040c0101f1101c0804041c45030015410b00c5c080140784481e03a41804070611050390011402c1c0340b01900c030404561090074500340a4030350111410000c1d400025a40642d02c41039005014161450088440c0d41c96000c00d03004001d002d203401c100050100f00c4403070 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 712688678 1250 712687428 712687439
    0x3040515180429061603110a1e0c090504030e010c0507090c0806040b0d080d0f021b250501021e24190b0f0d1a0a09060e011a0405070203040b040e040b0c13 68
    0x486007107c01018048070303074056603581c800844179454000408010100900c0500344004401024010b14044104110f1410f044d1402042c2c0510f071144181401404100003080000030001c040041502100030008424072482c000c1c084441500c0b60b905c5241011507401c0d02e0320b0081601c148041e8004055031424284803900c00140c8402e420300c18400c1d074203006103030180e1b00854603000c013001c0403000f0701119140f020042c00c0b060440b004030b0f9a0740403403207824002c40e600010503062850403000d9561414030007480561501702000e00c400c40703c0400c05a20524403201088060082480c140243c01041404080c0f0b0100d6085158072640304000e0302411010342000c0011602450158042d00c149440c50980c0025600d002d5079042000b130343d81e101030320511001c4d12500504d001428002e1000c41c440400103804a0100c010b018071455449011640d158001c008a800418148441e29111903443c45d152441d010211400e907172a6408100203407503001420102d40306003020f102021081810107 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 712689928 1250 712688678 712688687
    0x14060103050709080a0f0519050604020105130b0c01060602070b0906160c0509191d060415020c0a05030904060905060a0e070c0f120306050303040515180429061603 72
    0x2d861071081c0840ca0601041402e001e10400d8841406460402100744003480c2041c540744403500c81a031600a10040d00c2c1c0050408200150447e40902c0c00a0300d03503900c030f900d0381c0000c040345d030010403440d0380010030b00c207404819000700701110f07055001d960b04950b035041901528401c50010590007802040014401608040c28000483c09031812020194035100400c01c064401d0350603000e4038041d2500d81c1e40040c42070150503454980e00009500780060000025079900c4050700c000c10590003100044902442641581d16801e0684d00707d0b100c6108a0601a40781c0e444001094000c0b4100704010a6040b42070158038050301c0081c007011310061400d50035100160000c0c00c05410490482041408200d12105808105010ba04000f01c1d46030b40304000f404a4105500c5980039070400c0c0800c002a66030440c5100c0e000c4241000640d4070000103000300400c070200884140e1180c50310b1410490308866035030200d0500c0c0700d00e04ac890200503070300030013000780a1040b0003110020002d004000080c0b05 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 712691178 1250 712689928 712689931
    0x203130c0e0c0d230f150f100f27230d080c0a0804170c010906050d09020102070e0106051b160605091306080f01060504090809010809160306061401031406010305 71
    0x3082400f0480640b2005422055002640c0001701c064220045c803071802c4465004848046040b039011080d41c00842c0410304880c04066608140403e200f040f02105000c0e244500140c110003403d02e1003542442e08000e811040380c0114050340003160038070460445824014040060b00905a401c030b0b9882e642c81307030303280c0e800301441b6101c500803020380000103801780001e80040d00c00c082440c00c0c407003804140d0798502403000c00194100a0803520400c00c003500207048862000c00c0c0030010400e80d0f051b0005070b10b0061300da80700c40416260034000044c0320f9030000150001a075900c66031110300f903111401c541e03a004584445075980d5804002000654042c90050002a102422a40d01050603d03c8102103800303503070021015402801d20952140d00a01c58640501811141004800c9540c0c4a284081c004c0340302090510403090041003141108001042c1c1d042d060320000d100141e1a445c0c10f2001c2d0a01d841444201648502800500d40c028040d0340f60002900125400781daa40d4001103010303100 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 712692428 1250 712691178 712691201
    0x60903121b0106121e0210030b0d050f030d0501080708060a1505060d06050405060123160f03030902180c071104060503030a030b0901090908040b03190203130c0e0c0d 73
    0x80c240a0010751000a0007090f00414010f8100f41d501c0e440741c2014580400c009028080b40340340105028016520602d101d2020000ea243c0040d28248040201e80700f0508028050124417600c402d50701b1303e1000000034103240c0703005102070006136a240d6045945e01c0d000e0040c201c2c543c102d00c0020b01806200e0303114044440c4641e00140a0702c0c0c2d910041403480d444040404c200300c1d211541440036040c64041d0a07040902841c1a01c9040c40012503070b20382942e03104510724440d100103514510f188001032144403580d0490628447d070343c120314001e0300402042004900070039440031221210300414014134820301981c0502442c2000b00e9541411004181030140c3d0f000d0b603a40800f19076600d04001170181c50601d62800289454600104400c00105a000340c00c51801c00100780002025501900c0c1100e0b6421445030712070301c480c1d0b0080340002400c20418680d038404000c2280302c2c145202510099401544c510200c0c2c0d032200d400c00c00d1440e08941882d1f0f03d260030407080076030720340b1b59005101e040b1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 712693678 1250 712692428 712692457
    0xa060b060d0612051605060a0e0a03050d0504140a060507060c0c0b160909090203030405130b060f03070e0306040b1605040e010e090d0302120c0a1e020303090c06090312 74
    0xd01c00d001c540c21500c00e500145016140d1409440800904020340701074020440c0c00f170645145008000b072070314400c030700e2000200402607001d80c2040d02c9607000c51018591290036281200c05881008003507410620503078400490782038080740075090509000f401d1316401e0782c81d5403130081d02c2d880d42c0000d042d85601000411036100d0380c1c81c001c00c00c03804045004c1d000c021240302d5486c407843e0740208002400c0c1c022170802c034a424a08001aa00041118105d583c2502c0783c81c00110070300d14080081011058140e008040014074a01800d0340100852041103141c4600e918404c501c0c0c2419504c6900b00d800030203140710341010481030040e080301014048000c0c0303401450703d0f40351080c5c0d0160400070303888100078100c00002d02401d041c042c0081c1c2da001003c0c4c03504501f48010700d901c0e90000038010303000b9851528009030250b100c3e44901155580e0841ca0110070f500e410350550029039a5004640a1100f800340210b83e10451030680100d56151200a004000010040300041541e90000e1910319a64 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 712694928 1250 712693678 712693687
    0x305060a0b21041b180c02010b03210f130f080d08060f03010b12060604270809010302250c17030405040e0307020a030c18020423130e06100503030406020a060b06 71
    0x314000b44d118014262150300f0003034284c0140020003e41d4007080810040d0b90404039401d26940700064080c0c0345803031b0312180f00c0c0e4081d400d982580c050720405074500f450480c0000c240e29041c00e10b0380b0000444a40c8909001900e5a5600d0240c65004420884d00002c0e013001c040b40252420007807842e490b0800400010781000e4010004594804115103540305030008010810980307013a20a00710041325291040e55500e081903109400310030304000041061001203501c0c1d0090348a0f6041c0c40b800100c0240119520b10051907409840e0b43d05501141c3c00c100c2c00d03c0111307481c0003840400e51100c3c0028011410641400d0401c8040d00c4613150400852200b4004140981d843e15084070055010300c54000310b0905151900036400d445e2a1640050750041000b041045100c615001c581344140f00e511300c2242501e000101254082010441814244030000a0321000442c850340180520b22185035215620001e064480c021840f6400c05a0030510802c80480c0e0715401c40000d4210040600b45030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 712696178 1250 712694928 712694963
    0x30b0f13020919030212060112060e160e040b1821130b0309011107120c031106070e030705030f0303130c05040507031b0e03061b13060305060a0b2104 66
    0x420008156142c85903d40502c00c005506000201c490a0406000642003d6041c082c284d0000701080000401103030b95102d46120106003072200c2040da02640c040d48003000e03518132510541610983d01a03c0354514400840e581c0030b50f5000514005007040080c0081d1010002c081c00008a440d07030490301c5c260100901e03140195500780000207090300c0d140160b100e003010b20001e42100c011020103400400208281c13000b01d60500c29010b120383e1140b030b01c0013a6030399514086803800c06a000d2580c0d240f08600602c1546a00440386a81c628019400c503401e440c7e8a0040503564400300030105081e0308104085054200b003035501001d0540500c0040d003480742d4070790216003103600c00c4800d40006641c07030120611424040145550030a81c501d040e44c0511001c1c400070b62140c0d4090925140b0320b03650844804da820f1050180d1b1881034640400303110395661220040d0190a0485119200e8041450089441ca010000307075018800195040382c005440810a101f520401a01c02d03105011100001d501c5d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 712697428 1250 712696178 712696189
    0x30506280e0c0406090f03030c080307051608030123091503070b0d050123031018021801050102120f19140c010b090901060806130201030e1507020d030b0f130209 71
    0x100100c00c1d42c00e40e21454240c0c0100180f4150b00a418040d40c14802000400d9104500440c220740001910340c0d2a2a0601c0980e01c511510034203010b0444502103181c240203802001d50704a510007031022000d5540304c420140302c070228804143c3d000c1144d60105104021203901419445806070845010fa9200d00383e904403074004091441d0f0a544590044c082c018025403100070f18060b991040c803035060104000fa8841c0480c1540004041c0d43d464252200e0341c411500030840c907005032040d40304010045c3c4480e1130078001d001e864050310500d0200d00081e41313000115804402200c1920f8113010394540900004608200301400301700081114003d5217400d900108030914011000155450089040c0031103407900400c001240e07403520000b042501c1e00441c840b540b18038541e080f44d215804500c016002440581c1c0941010b10940d015410042c6205601c0c0c0c2c022005c0d0780880b154100c480d4411425250b0314079040b03400c101400b04800b82c505111100c0301228203681c0b80541000c2c0e50394041007 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 712698678 1250 712697428 712697431
    0x1e070f081201080c09150d151107051203071709031b0f0c030c0f040b12030301080d02011103040f262d0c250509070309050c01030506280e 61
    0x407030116a00010803400d1000c10140704206000e0303801710164a003642e0410a11003000700c2d41406000a29040001c1012405079150140003942003004841d55405511505420083c0200c41c688208114011200507030001e0700d01c600c00c1c07661009100100b110107001050700241050740f0b188000c1c001080310310107424020030f0f14200c8000402181601030300140c60210842c841078000c4c1c1000f006503045480301440840c9420303042c2c4010a001008002140c00c084008a6400650001000201c4d00350408601e5030892003031640248680090040106018130003070710002c149071984207a40c0f0025040e110707022003120243c1c06502c4815100d803034800080d8822050542021801d0880040c0007501e122900410349056151605203c540f20003d940c030b03500380910107542c140c1d91000c420b11404400001001d018040c0484e10309040000010700030340b400210071115400b5450814215501c80d214051044100420404d941c1c46110089101b45061149014030469080c20220720b68a140301c159 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 712699928 1250 712698678 712698697
    0x40338040201020d09050901152006070f08011401080403030b0406031209170613170f04030b0a02030f01090f0e0a08040f06140306060a1b0c090e01021e070f08 70
    0x2508146880d1000a007440704e001e809406201000c01e0500c01c0d922180a00b81c15102c6103041210140d0b00c014065a00841c0403015000030141c480103402e40315008036225007d00042d40b185810080d50140c1920640d00034012202a01c1803030118003401c0d80306030310a5401c070340a030400045104484020400f41c9265800c00da8484541072400c00c031040e0310a02c068020041c401144209850001c60503443c3c2c0c201030042450181303990740203018800d9624001e4040e0010000d5150f81d482c1038140b9040680003440b00792200348a680001c1d40c04a01402182d02c00c0c03141c0a510a0203030700f06000c3c10b000b0002c88c4464066550350f9000998038079010000c4503652801220b0554a441c43d020b4070b80140171064001100304001100e444010403501810741c0d42107101203c2030fa89a12040400320390520b070210581441c0c1068081c42e406018000e0920400c1d6446940c2c04c2c0580300e15141e03054240c5c45512507580c0036180480002c040c07620504081e00c195071140d0002d50171610035480b040501e401500f40c8 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 712701178 1250 712699928 712700033
    0x60e04030f0503103809030a30170109020c0a0201030c11031204021c0b01061407080d0506040f020405010509060f0f0f13061e0804140607170a02030c0403 68
    0x40c40e10040d0700380c2010314244045440510701b01c0d00c28003003a01c4008a2400a0212044003104650550101000190541403850b0941186080c05004080e002070a44c28450000e00e200082108202030007190f15041c025801005408219801140107203c40c1d410340742041144442c0c40310480062004100044850303041c40520304003401049601e0030205441128002c16074030071230003c0c1d00076008034115480c6041584462600c60008801440790000040c02c100001546c9040d42e40980d000c81e016007020740e001c00c6800ca5941d4000200e1017280510f90224000340915985403400074000c22220341d44140704c5040250401005101e50841c071102c03005008044bd110001c542c0e59000d01c4000d2500d031807c00a108070000024200b0019070706880700704016100000c042c0264880c071503040f08040401c030344041c41d02000041c0701001d8691007845070074988000c10510640c90083c1d900440800c0c9949240600d55030318600c070101c5148030300301d8428000c0f904040162010002c000102c02c1d40e0003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 712702428 1250 712701178 712701239
    0x20102040302010315120b0a021909180e0309100c0605040c0e0903040609032d080406031103160e030f03040e060a2301050306030a0f05030706060e04030f050310 71
    0x98107441c40030240ca428801d5041c03080060840c1511101c0e02c40d60401c1c900c07c0b150710342d0708149002e403041c81c81c0f02a001003c1c038a07000405601440100c00c40345414188402c0340c00801191060b2090201216590b500c18411021146000e004a89110800b03040c15881400303075956034001ea90044038152000a0401c0007003002c401112103d41c2d02c01410f1020310724040c2800800780a4ac8800d0002a01c6014400b41550f6000b01c00440c03660740e030280d4100114005154508a03031240c1c0280035210002c0c2c00c0c0b000c1d80e9840600041a603000341800080d540420403c2c2c1030032a007000f441541141c1c50320072410400b00c01d880901c0144090a0720480e61185880c01d01c040c8403024022b0f0b80b1101c99080c4608501d440c5003100c5041089401c024070b80b0540e40d89030200000d00d82080304201800d5207101c4102081084000401450070714400e08080c0300d040e0b038451228860031000c0318050301185002c0c5d41d00001c0313841440156489102c0340c083c0400941c0395140c1c40b91070207007120300031000405140d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 712703678 1250 712702428 712702433
    0x709091a0a0f030b0f06060f0c070302030d170c071b06090501030614061b0c0a0e10150804080c1204121a060618040204080105130c0509042f040c0201020403 69
    0xa41c0303240038115071030741e800800d880d6607078403000d106004040c50041440700000c642999104401c41c0e118140c0030780e0680e1914116580c2e1900c580480c80f040344284501304252051500840d041621030390081d80360071032944c0d60034544140f0303400008100c40e40c1103409040004220510403146c064542c55a44c040d100c2e013014005000c580c7d454010106182200401e00300550342c80040b82c1403807510040c0b008001024650044c80d00b5408180c01d40e000013441c0c0c0201c0c2c40a000200f45100d00103c0f1150340c1a00d503542900301c2c00704203500e441d0002403952030010340850445802000404110012581c80b03c0f21340c00e5603c503d070087e42008030300301d813626000317020b02c00c0c809500d002e030815144240c0441d0506c14001480303882110388c0340103403c40819002050340e0382ea0b0f040d98004c020b0b100c000e000c68a0814508080ca00c04103108a500010200c1c1c089000c0c04c02c200c82601c1194081c10441c00c09100b01e04106d9041c405003240c400700c0440801580440d2600e0080003001c0711680c0016895034110b1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 712704928 1250 712703678 712703689
    0xf0a112401140f0307090902010e0904020a0e130b0711011508060105190f0e0f0a090506041e0c03030201020415051603050307170903090907260709091a 67
    0x3503032291140140c010114268641a5014504542c9091100080240d515000c22245084800441e606024403100002d003c00e060300320001181c400da80d050070007815681084007003030081c2c0d03001e500000d04241c10b1050391080d440c40c50700410159005140e5001c203550b1880b2501c01101c5000c002070400000b138111110900500c01d101006200300f010701400e01c0c40d04c03175070380c01d051166a1050b00c0303010300702c003081142c03152050181c905940b0b81200780740c0f04d07030038100c2909047c5d40700c9038400c8500d00010600083d503c1035131403696109015103c0c0c0c3d201d0740c9800710a120043c2e10703500103a070300058540000c1c421501d0440154420b4001684031440c0c5907113141103a40900d01d0009010081000e260381c412028a80c003d4103070b040c10001d86035200c1850403130341744c4610f81c03c80c0b109500e10018411185ca002018103500030040f1510318840c2d80b8420219804801d0201c0c0400030549000c100e4864601215602d41c000030034a000c0c2052552030f010036083d40c11a070408000408254156409030412 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 712706178 1250 712704928 712704943
    0x9040c030b2d06180709180c0f180603050a0b090708090f3f040f080c0a050f09091212012607060e0301090c15020c19090f020f0a11 58
    0x40c080101d45910f00704001c1040d080502181580c0010712200141c00320b4020b903692000740c07410260420b400c40004c0c1d0f200c4000c0c002000740c0404600743c00707c040c00407440b580740c0300d18a04003c80080107c0f032400c881034002d8403000d80a101a40d4070383c10328000c981c4a00c004c4038410f510543d2003030034500f0700c4c00d202c40c00c0820741d8840440c290400c813904600016000000c801109052000240303010309079201881813224003a82d00d900460020f000103240f04640c1150083d5403209054907440007140080082040140c45006d8001c2241d81a481483c03900b101200e0344240f00e0030645046c1c240300440881c0c96403041d2104040f8000381401804040681c0e9040c1001500b042c211101507075036825259076880b0544258000c00242000180e030341e031000c1d004041e54940c02540c11030110f4075156491207801c14541000d0052140e151500030340c0c90891409030481d4002400545528100303100c240c0644545940c22404a4007002269001c007580401080d003400150b4402040c0c0711020000c50905030f2 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 712707428 1250 712706178 712706251
    0x702040509010525200f07180c0806090105100c0b0106050d0612020f1e0603010b0307030f05250c020a0801090209011215090201020a06060801020301090c0903050c09040c030b 77
    0x2018420f243e49600410401d601d48600285445c00c040c20768a1136145c405083c46180d11801500d07000611502c0f140f0f80940243c0320003805201404405508960401f07084034940c0d80f110301d540040213030703080c03011020380580c0c0c0328a455804004151110341c507a030b00c00e9200600041c1c0004030b0711410b42c181d115610280022180c800c2082c00c9580004404505628a680c0309241050050142c8143c000c20704510102c041c2c01c940e2a0740e9076540481480d041256010082800d001c8a0107003a030b140c0c4038a921840d0080c0d01d4007426016840c851300500790817640b240501401d0201040541d9070b0b00101e070300828103070001068114041c814480c20140692140b1603040c0405014000078129118403c607030141d1910002e244005800103e14003c00140050300a40c6840c8001c2000b86064000f035041e542c09040a100c0c04c800803604031511754191001600c2070708000441d004510340209100d80140c0180014030300070742c0b00d840d00c0f003945000b510070711050228650541944c1310710342d030018000307017 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 712708678 1250 712707428 712707481
    0x4030c030e1807270b030705090d0c0b07020406090c0f2703050309011704110409080d090501050402091806010b030a1d010b130b0315180123010e010b04170307020405090105 76
    0xc2c170306103000b8420701014244505100e00031400c01590f450b060704140240b50020303e180e8403640d5a80e013100055000c904140d008070b00304032010070380e0b070780c00e0150710080821a580c1000c10310f420750044071506040100301020001100c4000b801d00030030840034014602447c05180c0e40d003542e200141100801c0690481038100d008100004201c3c81130700071100703c0040d40d000c00c90000f145014045445100098600103280001c040c0500c00e05500c9980709030302c00c0d40c801105031a05000210031032221882078a241c1e001030014401c0b100a84042c642103541c6010101d0841002a102051446155003e140c640c3d0340d02c00c0400c6a19148181d00115019020104950740026021944070604241262001c14248000c2503001044409801041c104080204041d21800f442403024030b6110802d2204200c256001280a010704c840a6040b55150030030f162606150940301c80024008552004282c0020b004100241c1c0341d80c0a001d102d141003100003e02407a20103025102d4038600300304000040b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 712709928 1250 712708678 712708757
    0x30501080d030b0a030f1a1b0f07020312030108030a14030618060120010c020c1f0f0c062a0309030504120c080a05031209030304030c030e1807 63
    0x36040480c011200c0c0400b490042040100580480c2088000b540010700180c0c1810300002844201426052061083c0c03103120b0b041e1312035140881c010b484006409000d920100002c40801d223902c0b008000c074910103800e5441c1c2c2c850580a01c1e0700750300240e01c20030b1103800000c1c8902c01c2e241d1004440345200820650300c0d003542400c0c004500b2040e4108251341003c401400810800e0307016501c1c0000344e800722a08005051452103079680a0f05032281001e001d84900828040c0310301c0c01c060004242e011854280500d129040021134aa584040303014041c48070310708907040031448074045c28000303080303a0301030b180c100d0000306199981300380303050b0410101890940040300082c1c1c003c0803a8200c40784990030a11600703940c200035841c840c05500c600f0041c0b05507501c010401c10040080c0c229209134900c0d2025a50310940320079201d100032500100050368405c10500002e000340010000c1031405403545031010b4900032500d01129064903a02e0106500c4c006c00004d0100940113440d11240005230381c0c802 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 712711178 1250 712709928 712709939
    0x80705040e0c090a081e060c0936100621020a1206080d090e010b2502210c1806060d090b0f0402040f0c200309041d010507030501 57
    0x5034000e900400d0300382400c800200d1400045407054802c82d05004000b1a82143d07036117041996460301c0030040b85141e03101d01090021480100d80f09205480c203100144c584103010003080420300c0841d4140c40314410794900b10701504c1e8078100031f000d455841c440e03a449905114608180340d02440d40001c080040041c100c2ea0f141302082e41007400004000070150b11420388a90a84440c20340c80c1800e10641c2ca032020014401c600040e44850b54001e0b03898080d06a900c031004000401d00034021034038030b40003c0114070355040c0ca044941030900c9468a00c3c00303100d000d50f400603545005084444505404a00030003800360740c14000c0c10b150030301c111101c4905194402e203080050000601d030b10b21400020030200ea00003403541042101d1fa034802d80040c418604240307004035180d0107980c180c1c05549080999020b1265030701c10b140350900305445404d065110300303044c8541c81618020b69040c0340000d006504040d20745008413003003000514611890320b004801a5800c6030ba0080c40b5000301070804004112 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 712712428 1250 712711178 712711187
    0x60b09040f0f170a0507060509061b1312060e010509030a020c090603030d2d0218040506130c03020a02010b040b0f01050c07030c12020118030b071206050909031201060807 75
    0x241182e200d000c81103041030a08290001c01c3c041000c103004100e002a2286015078000024810070344182020802038490074091135940c1c508403495140c400c180c00c020030122040340040e040c0510300c81c080c0a00c5545501207000c00030400345c41100c1c1e05442d844c0b5000c1051080c0a41d03648188010021030030011002d10013907030b40183c4080140243d4914010401ca501d0500403102c02c0e034822001408034908017400036520f944210a11000c0402042c00500c91200500031111030010110316800702154940030840140b00103005a54072800d80b004c07060101c26940151001c0348810349005071903074010480a42035a0240c2112441a89060035508103950b03568148052500c00b868400c0c0c0f00e17400d0795501850600240c10180800141107800150100f100c0b00f4442c10a100307a07640300b05500c02034a184404051030000a11086840b03000070384030341c41480568040d41502d10085840c564072030100342034100c207840c0140141c0001901c42c1a804500b448140101003924000c0a1864582402031 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 712713678 1250 712712428 712712453
    0x6020d0e1204050f03011407020a03090e0f04061d011416050909070c031206080c010905240a03060b120a0e0a030801030b1005090f09010606031e091707060504060b0904 74
    0x41c0f14000342c01c130b5400705031801d510a0490714070080c0e00c21024200f0010203591007030007240071030001ea01c5207004074805030820030184c01440a8070702481c1c41c3d02c80e9603640010380b44100d400d54500305448007104138a0703070900030f07011303a6202da0701c900703d03507080800138020032802da01e10132020300400f00710b00c260300d8540d0a110b42c5c0c400400d11340718101000e0b0345012620740f45003000310050310741440f40211300400c1c04220801141c000362a1050100c1d030742d00c24030684180d0031041803405919a8500114002c1100080c1100e1410785000280180c6580d00b83e402500700c81c41c603802a800700002c20a42c0403042c440c1b445050507000080046110302e40c0e00900301171050100a00107000b0101040803004504541405410300030a040094689080d21603d80c24086584107055820101c000030424000c6c480d000041d501141c2d940f5890003d141d03080c1c007030420740c0e5088507180041070b0b490b1401310803180581902807088601040504042c01c140c8181c0e00b0504490303214403d0747e001c3c4800100300c80c0894 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 712714928 1250 712713678 712713689
    0x60e010c030c1b05090c13060c05030304110a0518010927030507020d081b06100f0e13050105010e09070807050a0e130204061403060f010602121c020706020d0e1204 72
    0x10b02c04404048a03124550300c0c564085174008103032030180100903045401134101c000048490070b0103030b40e5419040b200f5114104000c0d2041d0400c2000c2030100d48950600c00b82124041d0402c545155200702240388800d039220b030102a0f520300801409080e200780184406080c007003280b6001045d90040d06d004c8400600001402d00400151480840d120800302d1200590001c03041616100b46d0fa0428a64010740c2208000070700560000590508a0185410541c0c140c1c4034180e080e81e050a0803452080c0000e880d2c0c85140c00038000c90783c009802401900d010702000300c5201101d09080541c82c1c541a4a6002014117030000c1405202c80d4071103c04050441c0c00c00900081c0c0c80d20342c42d1303941c901d51000d2840a9002420a034020500103482123491140c09030a8040b0360284c1d465129401c4400f5082c0203040040e00a44d2070668514551001b5080c1d0f0051402c0d0b80c2c6201c0710310304034007040340d114441c210b803515004918004500b146100c0c01c580005000003a004000c0301c10819025403081b0b000c4c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 712716178 1250 712714928 712714943
    0xe031c0e150f130f060c1e0b180a0606120b100b093c01090b070b0414030409090b0103020907020d0206010b0f041802040305070b04080c011b080a09060e010c030c 71
    0x141d00c00040303c00d8481d00141000c0007840c841a8a6510007400800013240644407440d42c0c0321032407400d4001840c1042c2c0c041d080142d4485503141c40f0414880c80916a000150601c202015400850b860748521802048009850f4103030144528040503001d40007045483e2210481c6420800e409509084603143c0f801103c0c03003041e03800c43d900b50340c0c035103102c0d070150506203464140145500c0c60f80c034145a40c801070980b9814450380c0c1d240701d41440c0f03210f01c500040ca555502008500080da0a6000b86128100007040d2804c0135100e0072901c04550200030300b5100700c0103600041040d410920031968000c0c03c01c2c4041c0003460140c50010395aa08184601c0c10b204034006040d174aa56142425140a0080c13100743d4802c8916020305c29020b0f40290109440c540150980040c0d000c49880407502102c0b9564094001c1c3d104410054a4203907030803d1504100f21105600c3c0b0000d48204028100168951180f400003400d214000b0300d030808407000300341844906150980480d4205035007143e500d42c40900c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 712717428 1250 712716178 712716187
    0x3030702060730060509370207050f150c03060f0f060c01020a081501080609070c0204060b071209060e030a061a0303031003060506040b1e010e031c0e150f 68
    0x40d00b00d40011142000729540c2200100c00f081c0041034219100301c07241150000703003940740d01c20030b540c032040e003408001c0010b45400c0700440903c0290f144c0c1000139455410045c107080b095181e05007010000c00011005400c403c0d10002c0302800c0584040e00107011000e05400d52500c000410b00c200d99081d4140c3c4034100d40d0340c1c0c400d0f2070b55449003202c141c4050f410081d5214254410702525420043e6400c400001084180e01e41c90351040c4c5031740e446070302d00130590265502d46010036605a00b071524240c0c2c00545500c400b06010384013200800320a03129100c5003011808a03e0014030701c4480740c121004002c27101d6403894031a0b40000f00c2400c041d401420001d141e01521142c0380300007050080740740d0940008000c0000305141c0c8052041100d0007501c0078404c9641d0301d0b003040115250070740865800b10546074925080e0702e14040000108070181000d1b149800d91800080ca440f01020303030f000f06001e031028115400340c0e02070f0300503015032030175600c880403c2410842e601c928002e40400050300100400e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 712718678 1250 712717428 712717457
    0x1005150a0b0c010f150302120d02030316020307080301030309090b040e120c1009141e1b1306141221030601362312070e09160602030307020607 63
    0x1030264144440c40881000034038142c01d000c1d142841c5034441a84170b0100007504d40d4106001080203c1d01c9d00c03580c2c0c0554519030f20038030000e40c50050301422030110b110904c08800003485180040d4040d50180e00c41d0070000b49004e00740801e4030750080c1c50700c0c051403c0c4241c6480150300040c101c0042c01c48500690380704d511110a540c503005090822440090610300a8818010711580418413042c0ca181994001d400b2404040342603c0060214101503000440600391111220714003114030074000c20450b42c01c2e80d02c600040c10742c0d1290304050101c28010005101c1c0d45080d140c04145000310b80081c02c9210340c12500d8003810000c1150440e034002c000800201aa03100301c9200d040e201141070007450440c902032145801c00d50401c01c0c803050004003840800d50031504017548150580c041e40f420039103140c14090001c088220a80c1050501c03a1610204401100403040780c8503130b003078138020a00e00e1020404280712002540c8680b0943d0010014003030340c41e0740403030403590100329070601c00c1c401788100 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 712719928 1250 712718678 712718681
    0x60203070c0204050f15060c0d0f260925030f0f0c080a02030c0a120215160501020c06060a031a07020a022d01050307050403060f0209121005150a0b0c01 67
    0x107140095016251504201c1c02e00300f1010301d02e0040076038908095440007103205100c03081c0300c2c4031513420440d40b00c0d04460100c0381c4900c13010324140f0400d01c4d000302e442d010140e6400340c0d0441710f030705044051483c004101a401041210b4400364480001d07003985c000300e4440d0003280c401d060002500704d00500c0004070520156003a0503259590241c0c0300080b046d40d030000e4030380b10441c4c070008070701c0f80c02405040d910510b0030090f482c003130350090300701220840515803c0181c60b0700c4c642c10300e80700400e06100000c82c01d0f84e04c40c602e03001a40504005681c802a44030b406040840051880c0c2c40342d03a40d00f0301800403481d8901860a24840700d0f4503540140c60f40303c1d043c0d01d08096a64000d5000c000d00842407030900c0124210a140f000d100c0401000da9940001510766020440703440340096801e010420100f40706801c560480420584014508000030b00400e0705041c9107055400d40b58424200a03407064401c0c4201544001e18220221440414000103000b03c2c40f00d105000c0b003964080385a81e080d1000303 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 712721178 1250 712719928 712719947
    0xd022d040519270308040605010b090f061c060f051f0c02010c06060b16060b0f2b051e12030907030303020f1c1a0103020903060f0c12011e08030901020a06020307 71
    0x42c3c038010070140b0803071800611203041260201c0d83d003070610703000050409801c0251418101c00611003589118004284411500700c410000d485101d500284000d5280d60300c2a80003030088159103440c22414181030000c0078504c2180c0d40301c820346d203000d5240907d601030b1071002d00c85e509180c43d039070660300340c21315034044c119507040100000310008080d4011040c00c04040d240d917104210a00150202d0302c00c03c8021803508002d1a0446036103010802e050b4620040720310707030850501c01c0c10740d464039a8603064544140c41c2c2c01c5c40d01d0214640c1d1102080101006520b41c4246a160702d140307145400e0394026191800e900c801130500d80c000c1500e02c01542d4100a40750241181813415244130440d80c400001340812036030541640601d1014024a075100703000302c03825614007a000704415180d4502c840e89507580103282c205028014000980c94031140f004550080494249400707070745113030011541c3c40d05201d9100140c1c6900030050410940d07000700c0c800c0d802981000b801038607652a0882690341107032 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 712722428 1250 712721178 712721231
    0x31003060c02010603062702060903010204080109050105060909120406080703060806101404110714031605150106091d100f0806101a040b07020d022d040519 69
    0x30841d8207001d0950550202045900505043c4162030402c1c8803804c6c03600d030720200c01c90f10342c402a65030400340c2000401060415405000185802d5894092070708540421104884c40c5e51180306105482c41c0030f00002d41c10680c00307c060540d20500340c4100d04640300f00e116500500c42d10800080049000740d001da4000c00d401c0301924490315215aa16098071981e014000800000d80040c0752903040904c22044100742008200f494000c907605c501822030342035144068140b200704006a00750440800031101c00388901c0041806140003034058030003a10581010741001583c040030056200d2640102c480e24014040c000f1003034555241d0401a2030342da0300140321a600c0d0703442c0041c00e1000060141d100714000090f40320616104c0200c508900342c20316084031341c0d243c14002804006281c80080401a01c001d00c000e0700300d02c0136400b02e1410580750900d40100040344da02007085c05101d110700300c01d001c005c403070810480c5000c1d2032780c0d900303580690300303c0088607603400d080700d00c05191558060001d038 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 712723678 1250 712722428 712722431
    0x90b090a020909030910181d010e07020109080919080607021006050f0f27130311061015050708040e010501140c0a0308070c02090c041e050904030503100306 69
    0x500152450354801100900701d01a041c03a1001408102c004420f95914507030060502e40c0d03011714118100c44040981b5003075a138105000000180c41f5960b8121107450108008a04910b9032402805a002c4440100f003403081da41081c4503440001c0403041101c3d0107030400c880584403607114200d002c09103c401c3c0c010100701e214480600a25503000510f2036180340c00d0761801d000d51910368003440300403140c07000703000c5e000100b20b910000c0510700701e0b91100003040070201c0080000ca0300304031020b8044040d1030f00d0441c9940070710000c061640c880400100c10039100c0040207942003201c0b00d80007107183c601c50a20041c2c4024014850070b80f040c030841c0c40c01904044007944403134807008118203443c0284252800302c0c40c21650f075100d4410250a40d4100460320020b40a1072102d600c0a47c0c003164000c1280c401c00c850320000000590300c000940703002e407000c41351654a450900c03010b122500d101d030450350090540a0302c01c01056507200f64884c0d005605140c1552280c9402540c01480c8100f03030001800076 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 712724928 1250 712723678 712723681
    0x209030703050303100f080705220204030807120206060d0b0702030d1e05010f082104080f010c02010518100c0309050a111306080d0c080c0709020711030c18040204090b 74
    0x40400001341d4020003051030514141543c58101c0d20686095100d101001d410200e003c111500d804031800340300340604c84200204480f2190754404136800354004903400540030825805004401c014203070030103028001480c06040040026a0410070316200500302d1407140005001e0760f01c06c0c001e4551188011105201030501110400e01e4043d030100701d041c64174900070000942240000c044001c41d2854800346c299080d0340d500407916001440b4441c85201010840001d40c5103080008158900003000005074094000c0c500038256800945041d41200d0000d6054a00c0c0802140058180741400c03000a100111b56505a000d00352294016001e405201a88000d00040420151407128112011903815108001d140201c844a01985810b41e01000964900070702528a07a085580103848135402d0010b9002030070300d45015a04400e01080d000b2504008000030f4003d101c2500e6400ca010389003545031080400c65008003610311404202d5941e010034150344440d40203850007504800f004500c1d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 712726178 1250 712724928 712724933
    0x30106030606030b06040605010507150b0d060f150602070902210c0301080f0a030503040f0c0b03100816060503043e031509061f0b03130311010903080406050a0209030703 75
    0x2400b05110540fa894048400a18070b450580304840669005031284c0c0c1c1440d425840d07881c09070140c00c1050740700030754401c40510f6070340d40c1c2ca80001c00075201e0302c408a91402480804010340b01407a03400e0302135000084e01441116008645901500c681c0c80d001a264100340100071400c07002d03034484046154014050202d240612801581611ba01008588807502e0580500369502090007014000030340038004500001d003c07102180031180a2189810556201c02d12541e0f1a802640c1081c002007003941c040191b00301c203100b010030884c20803600c0d452103450a4800352492200610082c107031809500100000030542c0b000b0007210441e030f448140b40010100c1003082020f000100603100340b0800d4015504411401d900310311030801c41020b020076469101c85842022a545008445406000008a6400080b601a40c8100940c82c54580500e000d07042c00303002a82040409143c81c0d060549502c040f0750080401a086030340305c0c000041c1035590602d41d10003070140082a96050141d400004103 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 712727428 1250 712726178 712726181
    0x150f0d09030c050f0712110f10110118081b03070f0803060405131101110f03031f05010c050606010815040c0201060302040608010b130b0303090a08060703060914060f06090301060306 80
    0x7450b620420441d016490101c1600350b40301103074820000103044018074a40080c1c1c4206541280ba8406414088000c3e80e00c0300042174074000341c502000007a95242c07142c190041c240110b501407415081444050440ca8486107520b1084884540516514134908800301008000326007400e50031407002c0500c83c0081c81d1040569100ba0303104c034412418000481d201c907108202c502440f40d400112006a41000c2c001551807088a40c0320034a540140121300e6807400080c80110b100d044600b01e20302e0784540551911740c100380c0940100d410050b8110b414000100300054064216609003400c00d160360780c0560201d00e500207440341d40c0c0c0043c104200110641d4054000c80f0990b84201c4050091980707890740c1508982100c030302a030b4458419032480c0510047d66000315031015028064070326000c800c401040601c2001c2e44441d0f080c2d803042c8204110152301d40300b01c4015200c501d40c103014501d40606214080e0401505031481014000340c4107509580d44800c9920f4800054021311480c2e50381d040100 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 712728678 1250 712727428 712727447
    0x901090e0a050709090c1205070513090207050f0a150e070b0f120601050a020c2202040e1906050108180a05070f06030609020910110712120f020606150f0d0903 70
    0x101040d40761030007040ca0780d5140207818086c4910b82d11148642c602414000241c03101500306404d200081000c1009008920250000381103050000b43c0d40e4030491400f0f5160020b61011b640058004002c40300008603144181c00403e295444003003950320703e050300a801d1010300c0d48a03040300c2e0700007d41030b00324080b90009030502d800f00011380700c9541ea60000541d400d00c00c041f88000107802022020155107030140112484012646046050f10f1095002e00200d81c0150009141c1001076810801c1c4100741e40940d50714003404c4c98050100c1481c2a001a000e000b0107499110201c000802d80400201e040018201c242d07002003c82d983c65948481208110169004d40c50000c7c1c244800402d42da095070080f607074411005031010b240b0102d070740411104144070b030b03141d90440d0190307003000501c800b0700c01c01081d901d500810050b4801c051120380540242030040c400c00940d001035013048215603510840c141e507180000781c041e503036841d4a180108903124480540c50000e14001c000c90038107500c4032051 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 712729928 1250 712728678 712728691
    0x4080d0804020f0306092a030a0605011511060402060f130f1a1309020c100203070201021c09020d110d0605010807050a061701150915081009090b06060901090e0a05 72
    0x508640012400b81602d551044030002c1b1039500c045401c0e01440031080481c04088142106c03c0081c894240000381807008800d4150b914a84581c0184a180c03e94400c2c80d801e080c040c100004464005100c0c0d60710b6110081010384584400301e0104104042d480442d1800b20007880000c40075a00e98008520501c0300c0d005942c50040301c441390b00c000310710070808c5485a44400201030066131514403050041d50001d10080c416010320304104030100d5060015602030b40319600050b8881414000b00340403a004200401d07d00c0e81082c01150242e10b412400100704c03500001e22000400180c400b0030700c40380240c00c0040c070080c82e200000804660101d01c02080d44d108460410b03091360340d0941140d601096500403203410608500400080800051000750080d150929101580d603035159601e06000d240300c0c50010491450800080035280c0301d0701000f41a4400d802c203c03445a6442d501411140100800e028000001d02c85607568060700d8070340d00904403180b10000505d8440200405054141d444 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 712731178 1250 712729928 712729939
    0x5042003091612020d06091110050904050c28090f06031407180b1c0513020a05010219020d06110307020a0b06010206011a0a0e1009031103010c090302090c04080d080402 74
    0x708142e0f10041820007466002040755400d48882d4454100620f081d440440380149103401881103925020112241d50004c0d071160f41c0c480740c000e0140030a8902c01040c43c44482010841c1074203c8589401c008000318203802c9000012a8440e000ea07240700507908002030308040f03004001600d079819003203195403c41e140d078520030a0300d501c1c00543c1d4a418044040204c0d01d1840c10a0107003280000c080e003048040345410551810403054a03404444055030088080303450070220b002542896210710004100038801401303901060b120300e800b1484c01c01ea000303124090490f0300a040c0f14490b04489a40340380c2c60846a03a0b41850080650380c2c120380708044491031100400070b00c1541c0045589070482d14582c1c201000f1111003244049564071201d500c0d010f2011214402400742c4031207094191140c40c5032103002c451401c50901d0302e0a200025a41da109a040c4945040c4803588200d00804903035042c0c1d2850425111074211070010b005a80013241d50b8400e003000e139054036920640c800d000700d0080d1070 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 712732428 1250 712731178 712731223
    0xc11100b042720040203040b221e08040e01091d12090105030a09050f070f091b031107240f0902010c1101180801060e0c0c070504200309 60
    0x1c2140d1030600d40b0202c200001d82c80356110110b440c03820a24010f40d030101d66840180400c030001402c85c1c1080d5001c1c1e902400b00300c2000b8038803251803502039020781c1900302d031341c0017a40c0c668a01d0505502e440c06c0c03400d62903504038007108001c0d0100a9401900c0946e6a4014941e1294001c3d03000b0240c1e20150b00300513503544841c643c010408511005410f042c1c0c06194070f4180e40300c006503901c0d8806072000c41c03190b41e03441101d0081a010700c0160103c11509000d4072030b4628100642c20703141d0898005e001c00d00e19014040a4034048429540512411400c2c0032481c81414180411680034800c00a00b84280180550046001600002c0400e64450504100b0340c800d032000d03101110699600240422010b07250301d404601c10b41e101a0048005260980340d6058040f6000c05c011000d9000e5401c5a4460304148107403608030f1103107a0b105030326450150814440c0c4400681d03c101034458580110b60342c02c09044c101802c401c0740d8582484004c0019660304004075001c1c1d4444c46400c8202000c0d02810 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 712733678 1250 712732428 712732451
    0x30a0e060708180105070f12020f07061706012a03030c0c08031503031308060a2d24060f0906021b0402090d06290f010504090c11100b04 60
    0x50680380107a401120007414514045200c5940b0060b0070021070500030248548400200c2185000450502c10221400310040503d03010785024411012130082e6008407005000d900d6001100054814181d000350055445000059a0f0380d210400c5400e0300301c2c02c030350303070801040c80c0e002d40420f130203200e542c0c1049000412a0111101409503400400c1000c042011800c5442100807240e207079403004003924600500c6d00c4c1d440c514454586d21220341904100104031110b12180300d26055401c5035408464000c040069451908111004c102145a520748048590000c4030b82c40c4011409002c00c20030300c1b26151032001e041520552161800108400c00105085d0701c0071840c01c4151a1604403100d00e420310b2000c120194001da1411508000d460140b0b402042e168040c400102803e450031039005070392100360030307410b02881014074010300014074a20340590340b1404031012a6440100007034004200c2c5421a9130103005504181c2502c200c0d001da9000d05680d41c420b44003040704580c2042402d00a0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 712734928 1250 712733678 712733689
    0x20d0c02250308030612070512070e0609010f030b090109121e0207150e010203070813051005250201110a0c1403120901111216060e0f0a02040b01140c030a0e 69
    0x20b0200624a09051000c241541003044515124549000903501095142c101144041c00080c1d000350584d0320111003000081c002c840300300d400540c1034826605560504040c641401e503144002860740b041400081e000703040a61100c1d0419500c0f00a2940c22510000c00611030860700410310700000a8805100303455000003603400c201c840c1c04421480d403100c20002528940c00d4140314506500003049184002a0200c0040018003821140c00801a00f02000e201c0704502680c44041071150800c6800c05080c1e9003190540c054001603606443d0740c00d9403004903040951000c14114921403080c5903c20450401104e80c11365100000c602c000c0d041c000b08041d91070b4800340181c4d0046004011001042d4411001d907003c3c1c10411080700c440904c0c0304c480761080c2c0d002d13030540e031044007411300901d003009254054404e2598000000302600c100b04400541c0300d142480000f4811699038040802d60790080c200c2d12844440c1c56034407911442c00003c02a180d9014599200004551076941c21051821 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 712736178 1250 712734928 712735003
    0x70302040f05070e090a0e01050c0301061709030301030807020a080a0b07080a060b0306090c090d0302030717090105121009091b050105070b04060f060306090809010e01050418090204020d0c02 84
    0x4681c0c40d04006000f01301408130382d100103000c210300a40c48075003200010500740a811301600307900191954a61400c0300c000c0410360140683c1c40e110141506002180c0b02c004140c03410747c5d812042090b51a019440000c140b6a01035000b55018000c1002e07107000d001680401c2d502c507207170710344604445580c2d5140c080100d802a024511078120300340042952420401078080c1d00c001d81c0e000076464680d001000410180d00b0031411401070780005107800401180c021048500c0c61244603550a007043e4100282030341c003170643c0050958008000254100c0d6040c100140240941c59040081c400f490424003081e440b0b501c40c0700d584850501000801e5403181c0200c0300d14640000c2050400d885982e900d902421070150f00c002c00c1612458080040780a6205402900b4419508160780c0c80d82c00d40090080f60b0b45e00029030500c0018001081100168510700c3c032050b801041c00150304601d48000340c001c1c0524224480ca85242910001c0c8141e000101e1880b5080303455544035006421400a00c1000803 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 712737428 1250 712736178 712736191
    0x5030a0b0a0b0904080403051002040f030201180308180a0b0c060c07050f071d090a05100915020d0203010e13151e09050d090f0b0304021014040305070302040f05 71
    0x18008900208208054003038000d65459008181c0305500703000500d01c25810380382a110b104000804100b00300040003256a40380c81024150b041070314015880e50f084840c0d12001c0c2c1809040510b4000344010740c418440519404100281c550240300f2a10030489a07450746580100000c00c00441c0003460078041e640780389003000c0101f805654007a0526025006540304031420301c1908044030400030f0031301016026000f900c02c1c42d0803900b0340340035081125801411071040d64001440d21808030b5000300c0c14201164a44c41c001c521070899281240230b42040c0502881d80c10303c0420003440301c621a4004504031598a240b8581940f140245d4010141c600759005000b4402c103119100146100e42000c5550720000f9601300e128020903182c002620000a0216410780012124402c0c80d60030230402c030080c204040c0f000f145c06043c421900a2440060300c003911070740b1468820303818144141101103010005000840e11684d9a141c016980c584602080b48190706000c20615008024411548582d0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 712738678 1250 712737428 712737433
    0x5010e06030c0c10051f0e06034801020105010b13180b030604060b030f030c0304090b0301061203030c0e04050405061803130f030b06240c010b090708060a0e010503 72
    0x100c0e0350194a405030f00110060400340907030980300000100703600c651441045c5002041900884550101201a0a5803c4603c00d00d00c4102406200d03140010109481c1422489040c0a03c1d90440c0c0203280300d2800840080e080795003085421600c40e10001c20403c0c50080c0c0091106980300c08845407507018800000004111014040040c4074500e40c488103803000d01c07840003441c00c8541c00828181700e0126801c0c0e40c9907880e51000112400c003042a0309095581c10003450a0103500c03001180c480c422441603010b41e548408510b2083ea60a500c000c0040031005e40300c4259200754600a40601402c06003040440e00c00c02480307400e0b080c14001c983c41950b0203805040c2c41d03a038150020108071028585000d0610080c17265450b000c0c0000c0c481c10140040c240b1442c0315074a1071070240c0c0c488000400b042c0c02181c0200b0b07005114481c00407100c4801004020041d11861044001401000104201540141c0801c00e00c403a858005c0c00f2540200070076100c210300c00c1d458070001c3ea0228030a20031141c066 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 712739928 1250 712738678 712738681
    0x5040f2c070c0312022a0705040c020c040e0727050a02160807060603171b0c0a0e1306020703120e01060608070c060f020408030909090705090c0309011e0c030605010e0603 75
    0xb07071280c1901e03141c40744119801400c229205501b4014030400502d98018000200f400c100b07520010008a80103000444040c0110121031000a440f81d00817640f260050740c5803c4140e40c20003041c07001d03c006c0d00380c00c4103422001ca0607c401f09140c0c219900c031440c01c203203000d012580a8090303000312428801d4040a40700c01031500e98031041ea640c08080c0550701d15950359000f100190500b40c408405080c044d04060311011041c41005036a02022194603a590080d48038440d561100c3c40c5900072903880344078160495550742d00050310740c4440c4d60000c0c011340c8006540310826800c0380e05218030340380780365081060510211213182200c920340038000200310602c1c0000d00c06441500c0d0101d0191080101003000c2c1c014518150070398200e9046045582c001151041141c00c2c00174400c1c0c1d0001055000780850b6151201081900801810b602969500000018128403003500001d550b903107864445201140026500303801050525003000c00079007024030020315503211740a03015440c00300a2000d443c6 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 712741178 1250 712739928 712739933
    0x30a0201050a200705010f0c170c030c010903030f060b090d14030f13052b030305072a0b0c0a090504200304080405011e0804110105040f2c070c 63
    0x441d000500b825080020041c050b2102c1c1c1e181d12888545001c40341c0c028141c3c242420005486100054000f104001050031100041141c0d00c0314503a000920090003956000c0c8401d5a40c110b2262124454440d800c01c0c0c02101015031682c0030b11442402c007441006400d0711291603211038860003550580c062011010b2001280d45a040300e21461100b60403a0b20708a84010080c14540040707600623909803001ca0b080005050003c0ea156207000c100303100003910751001d1400862901c80c0800039003050781d50000903003500e000322155114140c1e10070301150910a28458280388941081d4200c80c003658050129009040003810b5a00000f015190084514241010b02000300003540302c0310340c08403000781d158108091141c011401035010312000d903035030380c20f00002500b400c071000581c1d007000e114280761b22481c661202c44141c00036401200c0f10700d22408a40122224082c0350455070000a071a100002d5004100c000701a09d076079081765a01c031300c5042c01c00d62210510215142d034042070408291100 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 712742428 1250 712741178 712741187
    0x3040303050907270e2a030a020616140f0d1b0f031707140304150b12030d05060f090c0a021203011205010e0f07120f020303030a14070c02030a0201 65
    0x107200d4210412030f00940d0796a4850690850801350f4803e00102c2c4016000440c60240124501155035030000c1c4182088141e581d203c000d01c081c50381d010513900254250442d03406220a00d8400e4000785001d03190203030484044140c1100142c1210303062400c044030501b214021500610f03125003540030b41500f0000e00415a03064000b965180e600038400301d14900010000d00314005290b00035902c114218004039100c100d13841c000740c04a002e10440c40840716015501034202c81d401940000310400c800308041b0b051010349980c40600d98402924101140003120010150081c055040c4040c000c5841d0032081c0100d4402000606812a09403030000380c1654500f00140f000011610448040e0031111540b0308454000303802000c0e0000b4480030400130700c602401128203400e01c06002e0010800070080d031594030704691007440c001c1e50981c03020005100080d032501e1101d41e00501543d65074503041c680d02006000c0822245403980007480880d501c10320811540480c00d60103401040d054145400645 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 712743678 1250 712742428 712742431
    0x2061501090513021b0303070206090705061b0a05100e0d0c0b010b09120708010b010801060201020a0905011b0b0a09030813030e06160f030f110c060316091d06090609010b0304030305 80
    0x2000c0e51340070030010910807103a00c2c9807200e0a6041014540321f061651000b030610a000d05001d40e158400034090045a8a480c11618200040e503107141e40c108141403082d04260013480b001c0c1c41c81c061211105070041c2d00e0340143d0180680a402d0316030000d01220241c0b04100c0b2480c0260005024600600034101c141000f0a5000c0b001402000124000303800d0a00c0c1690300d41110400365101e0361429120350704450107602404650009500308130341d5480c010a006074600c41e1070304101003c9641080c0200b550012003c0700e401c00100324081c41c104040001400b000c8104078001f17840c54000130080402d104014404580c950384a0b80601145401c200d11350b088184001200103034081120002550083d0304c098451217038840c0422082c1661000c0c10702a003002100409802c84144c000599880c0000c580c0d000000305816024920803410498203156941c012102e41040809141004030300901014801c0000319444003080c2e41c1e0b05c042c070141340020301c150000b005052001c540064000d0b0440e5 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 712744928 1250 712743678 712743709
    0xc01030e0a061808180108071d0d0809030a140c01091526040f0302101b050c070b0a0210060801020f040e1e0a020c0f0a0b060108040c24020615010905 66
    0xc0110f4041500d5850442e403040c444141c0301540040b81c4092543c112614a52019150400a0071111032420f090002850710490a10814103e86458200b1a14200796844010042e0850f04000707031a03c1c1c8202c03103221070043c007003a81c42070461414082d841800d031340094a01340e1030448400e500c164002c0d41c803085c4084c2040840c840e4401b0990400c0202d01c01c03584220301640c11460300060038100a420182c01c18545d10300316091030080070b46070582200040382222149405035482203000d0b48642040c002c0d40041580d0440000c01c0200241e00042c441102c1c03410140c1041003640d80c0700014201c1c801c410800c400440e041c8400c22000c0a1190728940c0070343c07010102c00200d1103082d921646400121a81b0241a5010894044c0808100041110310380c0c540000e0014800307a854102349008005c0c2401e0408c110384d800102005184e5034902d0007000000e010300003030303036030200030104801541020340d00501c1038200043c40704600176a91010a01c040c0c50381c803c13042c10071092050085591206 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 712746178 1250 712744928 712744961
    0x50f0312040b0f0c120913050402060f0f0c0102160b0702030c0705060d02070c3005100504020a030f0503030103062405040f3207170f0703091a01080c01030e0a06 71
    0x9114000b1014417903081c0c0602c6050f100ca0f660703c0c60004000d0380c04d400390804c01e0784074178100400c40140c6860040310040c01c15040790b60345418071003d04507010f00c20742140800035400401d0001c5402d076903540c04d5900c01d2290342d030035200303540780310040781c1c1e030302400521b41081e5202ca03800300a141031150041403041016a400362074144241c0302c041ca040e040d0741c07054000d54201e01d04002c240586a10303681d511a452017104521044640b100350b6142c0e403048060102541c0d0300046421940d801030014025035102c50100d4414110307091040d1a41c000b44400d6a40030b08100800c5201c018036079100303a221030210031040d507580c01d01d0305010082c22002c1c000e200c41e0355101d910200c2c0c440b0007582001d4500f000303001e40401a50303205c841320400902504000074030441903c1e040117140801c446030790060f0980d4000d00256929a002c602504075503202030400302403025103244120b101d409481c1a20f5504c1c0c215030105460390011012621071010310002c58008011000000300e007a0402080c10402120 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 712747428 1250 712746178 712746187
    0x4060e0a081806040504020c2107030c0206030c04080a050a020306060405010503190303150f0f0b031308030a141f0e010b0912070e070c11011d09040f140106050f0312040b0f 76
    0x10134105d9010800c81c07000c4d41c2c428912240340760280c640f12743d84204007100172400c21a03503903405031520701e510100900c14200400002d01d00400380c019900140251f40803503c0901c942e003005616000480e400b13034000d004200004041d41000d0045034100c3e60085c00400d60700307000480c2e00001e0281e8030720860070181c403550650004041415464007403d40c00c0fa08c4181c20b86846841c000740c2203954449a03002d6803d208000cc038002e441d91043c1e2094102051035a01d90301c60581400401c440c25006407041000c0040c400512408000500c8000248504885503511202300c982c00b0a424811880f20751020403032560b03103040000b408450240401c0c104d800340750b00c40100301d082c40c400312000e81c00034210a036060309114803085826036011080c241001108040070b116185003408a140030701401019003c41d0800c00300190003020740d03820602c1601003206200502e0b01901d543e2183c1d40c420040c00302c40e0502841c0c08a011070070f403c500c407030161401d880e0800b01c4d41c031a042512602050b40c010311 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 712748678 1250 712747428 712747439
    0xf0103062301060f09080105220c090f0c030b04110f0f0909090d021b1c02011e18091e180c0f03120309050d08090c1804060e0a08180604 60
    0x1d0564081d042d507807140044000100e84c01480c1d070f80241c0c0410742030382c104401d00441907601603040304603040a1203103602c0c486c6141072060441c011540520000c91528084e0000d0b4001540800c1c041c03c0c060383c05010307050103e42000141c40e008450940e29150400c030072000700e00b6550042c80d1000451080ba0b040003014800141e9050044a280755207400c2403a50100d165414892030000d140e200c3ca4009841080c00040f0712039903402000c1d043e402c01c0303c02c5070720207581c001c1d83e81c20310743e166003c54134000b0400c81784014013003000400e581069407140a40030a01d00c20500501803502c10545642156402c05004000586610740503405203901e074540304030100b075809034584080d010201c44150325500d0344c038011900c01042d0140e10f040501d001c400100243d00466a4400920b0034601654103071030f001a50380c140b4a40d038010030345c000210b01c0040c1004419110081c8103902540b0104507602c1c125041c80d403610354800d00146405810480501c21110303007950080c421802a01442c241510b40 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 712749928 1250 712748678 712748741
    0x1005060f04050a060311010203030919030519020f070b040302181e010305160f14010f0306090f0e07060507030507150204120503030a0e1914030c011508060f0f010306 73
    0x5651001400f03491302c005000b40103070400b00c1103449074284000c601e1881c1c28907840e500d815072414091a005580d50303804090520850030303211400d090001390400c8200c216000703580c5010f440318565143c0900f01c400035254845006030b0301125000380135030f08007107101224503009041c001d10301c035940e0303400c91801002c40a036060480d002c0c52150000f807690300881c020a80c2d40c0e01e80c6500c04542d41d542102c00740103241c4513490541d4010401c1c20a4044088211015409013403103400c182c2a4500c1c0c4902503140d40015002001546003140668150781d88800c01100c584c800c07094050b0100b4020000c03800090140710310004040500c0000506090702c5a504140134601d036034013526240e0000c000d0042c0c03d01d0038491a550040502d0061081891462031100c542d60005805400c0e50a031200494800e0014021201000c1041c4000c00020300820f24007140940c40c0d000d00c0c096480f400001400c4200306004e610700a0502c0c8441d20120307031842c1d0342c04014041203954241c00d1030091346428940000c4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 712751178 1250 712749928 712749931
    0x30c0105012601020901050403030e040b0415050a0f080c120708060103062c061515040f03051b010518040b181915140d1218060509031005060f0405 65
    0x2200500d0110904500c19510604100b00b074180680d01c100106801a80c00070200c0b000c0780d9050030940101d00700c240c000f8004107040c070311070354010f402c0c1038500c000c00e44180340c03602c00c1d21011076142c030025466072008200508203020f00c8015511500a0080394175040c000c0c407a01c0c9141c0c0007103d000c561605401414500d082e80704940040c0c6501442100803040c400400c103070201d4040c800244601c0b40a034582d5090050b00301c60400301e0440c080450303900c0703002041c1d04a0500d03000ba0f0b0703078869403121000c2281c80144001d480e02c1c010203031000700c03080004904020030b0780c1c1651954202949110002401041c03210540d600070303961940303030005489800c44603c0c288078401101c1120320b809a21a1034a9114014101030207182c1042d070f40421201402240941c0c42c100040c074100c494940206a849083c4900505120b101c410115581c81c0c0c00001103481c188200f51304469503542d4201582d0038010000e0751a03168010340005030700d03048140d0020740d01c000001d164040c41d00200c0c1c040740c2250740 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 712752428 1250 712751178 712751189
    0x30601122a030309090203100b090303040b070f0506010e040f201023040302010504090207082a011a1809190525030c06030e120c060405120426030c010501 68
    0x41407008005154220b0320040051114030020351452808400d0114921030500400451102c0428080c0f903e48080066401502e52078000396515211401c18141104112000712400e220300740010a90b100400c0d074003401158480c54043c2d144189683d8003a035046078031050f5034403c01b8034810310f11547c2c4404050085105640307031404058135040350284080a14602c0030301280e810002000180d81c0300e0200c500721500c8100050311248035103012a0f11b4810b0404480300003c02242e0003203071b002d404c01e81c961041302440080200800e04588400040341da05a5030f6404030030088a030083c00c040c54110b50340904c2042c02c1c0c58007a40316905d451800201040d05944903404400300502c400e1341e04642030415103040300026610740c919591070f24281002e005040401d03403100a03e84d10741601b0000445c880c090a40901c2d1680e50f8881c04507501d10080b10150764030b1040c0c1c04032000000c044e504940948031003580c0c80081a4115014003881c1e2905016501c031440100306c400c110480070321400d4040d01 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 712753678 1250 712752428 712752503
    0x50a020901030312050c030603070b0904020c07032f010e09040606031403040905010e0105030319090b030c03040b060d08090f03162d0e0f0601030f050705030601030e01020903060112 80
    0x4c071498491080b500c0082a0f050712040400500c94075a0703000a00c20200d0390200c0b907095440031f900300810042d000b04120030140e84110b1001204205d04030100340381c080414100000d400210310b06180e12103160703202140c0807030341001000c896810525a65a40700380580c1c0042445561b82da07620305081607580840301f5030740010070709000750b05190003202c4c01403404101c042d08030350404d00042c0c1c8a11581001c118409010030801204501a0720904010f0a0040c0e62640300d1074074403100443c581c02281e0031503103102c0c60000a8051303e070504000e07401c1508401c94500b0005200d0900a4400c0c4c0203034129414440e2902c0c0c510060440c2401c00042d110348540d03980544a801c150300c10005401041010740f0604107814031a118001e50403561101c52a04060380715191100182e000b005220390711901d0360f082004101886400000031406560280d804000304661281d003a030803405898011540364100328010402500001030190209016903c0800c0310b140d40e1308407640e0110100782d01030010 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 712754928 1250 712753678 712753697
    0xa051f030b060f010c0b130309081b1017010b0c01200a020c0121270501050f07090806040f0201110613020a0608010312120f0906200a020d0804050a0209010303 70
    0x1401d00703000385210f02000b82480d4600307402c1c60740c442d01001c40062850701d2155101040106140c03055440100400d054002c1c1c0301090720038965103c2035459000d540d40244403940e0042c1c84a886a42c418000404e20070381240543d01700a030060082e4410080022599240c07107952000703441e6200100f0341c0d2003032201603680d0751144440c06410594031104081c144242c482541c01040201c080700086240b031002d00042e0380802c441d031405001c21481c8182258545003034800c0401c04154841c80c095200454484220769072200102c4002c0101d00840420f0380205001c5400108160040800301384141007044803528110113543c0350041c11107444014102c103550300300640c00d1030030002010300130500e0406402c2d070541e1624070322401c2940c120800c00c9403a0482c0303d2104003503803040340d201c3c1130411309211004160422802614650840f0036002c0d60490401c0400c107180790843d402c08416402a0112407003800e42912010300042046c2e90034058451036600595a050401e4003071446601c2c0c26600 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 712756178 1250 712754928 712754941
    0xc0501060603090f1e0c090f06170304170c090405072c07080915150102070527070306080601151e1b170f091201060302090a051f030b 59
    0x2540e10030350058041c1480c102d004404203020001244041d070f0032420035032042881404024990400c076502510351108018040790f0a02c0c2900048002c03805180140101500d80111100c84410b0b014466619401044100f2010310b045003040f2922100300242d0302c215048801003803202900311400c440903040709606000b00b0001041c140150389070f0f507248040426401b10701d102c0b03482014025805010503080000c1450760100401808580c0c81505074140d82802c024034001c00041040050150259040c08201420088001c00e400810100b10401000d0028400e22504401404807402c140d161200800c801d20700704107860081294040c52a1070b81000e00c0024040c65071001a000d40406d40000c40052a51125080158407100017051925070914a805e018104100e260f0b4041c1d00340109016010314000d4014101001c41074a4450588841e450614200c540501000b1b501c07503101d00215a4051070b660009a00c04a08002c1301c00c0d8842c009085904400a503104807405182581040b00 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 712757428 1250 712756178 712756181
    0xd0602091201060f1202270a14060303070b18070b090a0e040203101e1b02070e01030b2701050a0504020f03210a020a0c290903030304060902060d0c0c0501 68
    0x72090040080040c5400c4c07110b00a51807200780b0500c410070400329022000d6696000141d680a40c040c0e08103528490a0310440d840340740700315111030a036032504540e400c0c40c07400c80c804540b00c0c9400401442c80d000a941c2e4003900054050407061141d10300350800c94110900304804000741a50203c1c198070740b01c0310707400c00003101e5841d000550380f0342144d03091000584002441c60146646560081035440b41034402446001003518003101c0c2d01d06081814248092707a81c5241ca0182d850390a880e82103465440b085441042848000c0410404100064001401c003c1140c6004001c2403000da203504031038000f03825600b013a203e840c000e0340c1c0c40302404110f2600349071b85e28680d101a0054044103164494078080350302d8814008800c0100002c1644066209105421000f60b2144903101e605440e400f12100700040030700e45802000b0350440d4440400c488000341d070209c4d0401001985196600d40c1e03005d0140240c4281241c0010742032180d41c254895501541c007102001e5900c2034124a000c3c10440d0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 712758678 1250 712757428 712757449
    0xb0405061024030504020f15030405060f190b0102070306050a021b0115051315030b012d21200f04091205250f0b10060801090c0e0d060209 61
    0x5803080c070242c800c103542080c0041c0c1d080c50101d08000800d80d940340082040042044501644002c072229407040f0a01a0f002460056008408960095035080a812104c1d00c00b5110003001c1909400341d0b44040704140c01c01555120184107440c4400d969640d1682501e03403d5818481080e00804d111582c0e41c0c0174082c1c41600c80a0780c00a002400c688441c0241d0601c06020b06400742c0744503075038030b0201e80030364020400d0f481100c2085580d0940c1d0b8140003806001c01e000e80c11109032035502d240c0c104003901c54211003403c02c4584032551989890708440b074898426101920700f020705400e03000480c21010702c001401c00f42d00a0322f050003c0d03101c00c20498175520f001891203145050780b04404600260f41d2200c0c41140307410525696400072030304040c01000140c9000c02c642490308036804100200e4111b8507140e03c6040801195106c2d806c0d6040d4803090742c0070f084000350482d0010846666150003d0300a0015030034100940e82081022410300c0104290590303c440d0001202d03111030a090f209036 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 712759928 1250 712758678 712758689
    0x90b13030b0a0e0f0715140903120403030207091407030b030118050d020c040519020f070f03022103040f0303020919030f031413090f0e010f2009030a02090901090b04050610 76
    0x140040d46c10006092800342940d0180000c00032000c28140b0148611011620b03072550040449030342c2490070a0140180c1c2c0540001c8006005202001440b40068001d070317199601621121340c2d66070340b2808110300520280c0e6000758035640359135142502c9805540d1541c0500c0c012400351104d401210b402902c2c01c0c48488506001e14984403c0118176541e074040100c0000303440202686c0d40c000c444004500c1e010f03020001e802c450604104104054002581042054170100f8144000490400c850510f00040724042c0c1400b110007020750020b8480e0b401401c074410300a210002545604119030b484903540e400881e442d0b400402d03070074107240c1c01a03000c081942891142d2031a168a0f802240c030f01c0102031066090840e190b00320390404000300e03044801081080c1008000318400081d8520190031552419a40380702010460300050598004590042c00e0140050a5940591b030a2100208000304411010355130781c10503400003007021400c0ea00445c0910010422030a280354651052083d65004 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 712761178 1250 712759928 712759933
    0x904020d0b2e1b1202120a050301090c110c0d020a15170609011a45012f0a0803010b0c101a120111040b070b01090c090b13030b0a0e0f 59
    0x820f1120b0104810640c103039201011400b0000f800005074949082d000361101010004034900b074a03950310201950480780400c80c1480214101d01041e20314900d44044000260003017040b40c66030703091840880d0341d9688007903c100307400da548490581105410211040010360b055188101d24401c400c19a034001408480c410030652401c10340e808101240e03011400c07085000701d110750b0341007001c1ca0340440e854044206030200000710722145903800780d50b4403480600480c0080585040d4451105901065204000092940c0d8401001000600c44440e002d603103120b12044200041c44200295000340003448580c0d44449104d09043d0401d101a150f5011281c030b400d440324a2280300c5d1481d202c0402c010b0314040b00607a00d0012a038090007101d007114018110001e80010035074001d0005084a90207081642006c0e622080c62100340c841106011002036000031060110324843c00090581c05062070a0761191603803980c500c072801318215440ca20103030380c50b154003070a20410300065018040b041c02 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 712762428 1250 712761178 712761197
    0x6011715090312040c0611061b0c070801091b080105070509100c0606030506011d01140402210c1911060a0222030602070507060908030904020d0b2e 65
    0x61855464040d803040008514003440400c81400040c000c0b110400b03c110516415882c0505005c07131200824413809000800c7d40aa0400800c0b01040c2180903166910400002c920403d019a40e127420011041416000c3c035000010390340310034800d85104c1c622070010961104801040c4402102c01036100c00026410a001c1140f103503030004c202c0d000301070101e402c40054100c110003107ca0200480d00140240e103070040c08018810000b41c90f074101c0704c4501c4904841d200390202000040300c01c4c810348241000185a1140710b141a40107000c1c2142c0103146100341c0c50412502c410000700c10f0311040c810745000101c100d580290018031400212041c20300c40070840007040320030b41c1c800d4002c01e180c054030703030114111900034444480050000a11000b55510580300c1c1012402035106078400c50315441490380008140c0e00950000c02204c4001c0055418114000c0902c8003a40c0640a10f011041d500c07810740545580e11039800c0002900c1801c0c041c00040340815284d00c2c21a4640000b043c81748501 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 712763678 1250 712762428 712762469
    0x9060b04030c15050c0105070305151c0b060402120c090a06030605130b0310110918070203030112061b020c0901050402030c041230030b0a0b0d0203060a08030a0509030601 75
    0x4201044911441c01c0383c0700610304a404441502624550000c0b43d42071400f8880300d40d50542107103018040c2420498900f0080c24100040031640710003a902e404d02a401d80000700328084006035000c1c2d0080c01c05890309034800d0f600501d0003411140551b903040c021803044186d0400ea546000941200d040401c486d504140c00101d0b0034000e900b0b8482d03500e0326040c0c45d40894400780103010443c0c210150901110302c21241c21000c41e0070000c051401200404659065081c00d20f240c41c2c013403032a60b0041c62640c3d00700200b440014494a0054a85a40f0392460007000141281a207101e141c050340548042c1c003c54041188840d03041c0d218038891030047c424801c4403034201040320101c034211210111422110b14080b44440031204881195003181c00302c1d03000d41074a04080d11100b8480303580c01c001152245040000956980c02010480082408656201c4000d54029034120300000c2c04440d04036507807001503107940d020086c1c020000314042626050b07400c040184034050664085c0c0b0305032400380d00 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 712764928 1250 712763678 712763693
    0x41b0f0f2c0f031b0f060301030308040b0c0403050616020f011b0c140a0b040c091406060a0314010b0406030b010518060a0516050d09080307020f0f0f04020c060109060b0403 76
    0x2141c48404100c448008940036646104070101d0540014007510500c209030000314041e90784281c1c0c2a030003050200c10119481c5000d208690607298551180350241c0c40369110042c6941008040da0940c03101044003001040c0c0070001c00c0d1003901c0468513001c40100d60540242041034502c0c40c0c40a5078141001c01101e09055501d40c10041c80034604135030700c044070b4101240300a03219260350320740e4010401c441007408124200d0b11700c5280540e80503160a56a0f210074800c8a9804080091441646d40412002e28205c0c00510350401c480c5001310318008040c2d020800a8000e0340b10301c8000c4400178081003c0e03034240c0a04a101070007402c0581c2444000c82003001c00180c0c010020348280000512004c089000d0f2064410740030504c40241000304e080d2910340d40c0c034400c0c5400e510101d103203d80c0000e20004001701f199602030b405458081068608028044080072120401e0b510400941801a040d10345201420b1035130b8019000705441e500d031001c10b204854290300403491000381000b0500114600 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 712766178 1250 712764928 712764977
    0xd0516080708041a03040c03171c0b03160614090409061407121104050411130b0705060f0103031709030c0d08240901140307031406040b060a080c0609041b0f0f 70
    0x804c0310309c03e42842a280c01c00d41c030441070050845924924091955a081d6018500100040d03040396080c03102c0032003c01d1a45c00c14821755002580341242c41c596101e500c03020f08103010015001107803840003907490318141e40c1803038100c00102071400c1c03c1080e125440010405841000c80e010082454a810010765a1040d401014022034850407140c07003000c1680100c405080da03103940701150036105d42503041c00d584518425103181c85a9800718102000742081d09048980c980c0b00e918281048522500981000901c81c640700e000602c440021500103100300742d184906c660710701600c0d190684200328188400418920b40b07011161513a0201d13118000c0d058190f1300307541403c00b038403d42000024034080c0940c1000341024407000710410780003400604540540e12480341040726588440500501d1020351050f42e21580c0060300485090030802c00902d02c500000e030020951807400c0000c24954400c404207640040c6041055402c050f43c0319100e842e00740020310700306841c041c0c0e042d00c10480d1401c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 712767428 1250 712766178 712766183
    0xb0a1b0302130518040b071b030c0c05060a2d080612011806060e07030e03090d030201062114122512030509010f09050d0516080708041a03040c03 64
    0x207000508102c9842e045540d68014400109008020704803c05100b42e06401550200d03030031401e01d404a65514007900071580705403a84012080710703820984040b00e0030500309009030781c190714102c0d0215403506c0e080000c02d154465512149801c00990f882c15143c00601440200200d4142c4080050160300c546802d4011000711504280011440442801082c003000f04901d1214400402c1041080740d410240403118a101e0345225507440e00c10903001d4034680000600c86400c1000790000c5481c10140f00d400d424000e200004070309803114004411140c20402d0894022001612a010440303074101510460001c0710107800410700c00d00d61100507000d10080c10b540c103c00500390310400b20b50021f64140d056049900341300f80c008281d101400810056a82424a5090180c802203818241c02400321465005e8014204100e1228046604c1d401001034540358100030000301001c15201c4001d27100250081690650300d900c1c00d0603411900404641401e18818140304010204009501d80d804880c1c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 712768678 1250 712767428 712767431
    0xc1605090a020309030f0406260709060f0e040203040c03021f080a0c032a020601170303150411070501051f08030d09030516050610050a08060c0f0d0c0c0b0a1b03 71
    0x111000c68130340c150b0142c4c1c1d0302c1c81004075012134002422948005051034a004000302d209411110398030120310b2410485840d000b0980e40d51080041c00d114240d012030312105850043c061070208000a01030740d02c1981c0a44220041300710030301c150310300200358031466645006044161840381e0702c080c02016008080481065a4070f591510440c001d402030350700d6020700d04e050210180741ca100f068412480d400300380010b1107400008500114902c03002039800c5070400c02035056072f0b030b40420f010301c1e90000940150000d4880070019800c042d0310000d000000d2003030002040da8070f803940480400e40900100480c102044250070000d405021048a10f002034501d00450320b41e00c24202511a40f140c50700d0500300302800c002e46c00030701001003122805020315503580030503240ea44d42003100501c01405429455040740300403690845030680200492511300c10703628144640c6c205a8800c5070209000000483c4c400d000380401c105114042d0f40e8000020703202081581e10303c162039100228013800d15810b05 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 712769784 1106 712768678 712768681
    0x140c010e0112050612060405060915040c060e010216090e100c0f0c0f020607030f080615040501050708070b040507081b010c171b01020c1605090a0203 66
    0x324016500e4848100d61410100020800034040c2c0368045d2070400d001080324400e0003001e01c10b5024a000c0c0140d450004040c5042040086958929410b0081007100040010650b98180e82c05481c004102c459454010707850031922520800e80346007040c40001e84500b040c0c100241d40c240784000c0d1b13002420584021400d45194000038170200b00c80c041c0c1c0200380c41c491500d00c65818000e20304c406aa03205134010400e580e006c4003098000558251440030000d420000103500444241e500c1c001c0510079080610300b030b015601503281080340008000c0309004101e000c1d105101c4d000030038a402801c051501e95070307801c00341c401c140c068001c0c0551203801c1c83c40d401c01c104010806855000d0120745076500d0010010f130041d11081040d90a005441065852031100c4411410480005985144050308681b07001c3d1240d240c00d59000a5a6040c022074560100c41c1e6003000302c842016882c1d = true := by decide +kernel

theorem cover : BRFrame.Cov 712589928 712769784 := by
  have h0 := BRFrame.cov_init 712589928
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712589928 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 712589928 ≤ n) (h2 : n < 712769784) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
