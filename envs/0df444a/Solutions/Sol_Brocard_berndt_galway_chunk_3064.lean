-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3064
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:33:11.143597+00:00
-- url     : https://prove2.me/submissions/13680a33-ceec-4459-9175-488b876d32fb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 550899280 ≤ n < 551079136 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 550900530 1250 550899280 550899287
    0x11130606091a0c070b040501180e19090b15120705090c071e0f0b091c110705090a1b0810031707020603091506060c070504110405100f020607 62
    0xd10824020400c451410481d240303446112602e0761444409083c80d2024200c103441c00c04281e608050b10016010500340043e580c0416403900046170007010054084c20000e11180d144001003000c0c00034410440c60110703849440c0c01800580e5801840318241e401c4c20b1140a60071001514018084c0300e20749141c0106180c009911021243d001d4001400c41d191a1889801c46d40815001e4483c01003e200c4034001d040241103c09101d40510340200b1594074601e480486514042d1040340140d02030311310310300441003e45094a00449074182030b8064180840f5031414035905034025a0700a0400c010400040929001080d980070400240c001000300c241c8113440e044025251951440110f000610004413282c5081d0709003074502c4403d6003082e00c40c0e030010f030041d0300845601e85190004160400c0114100003180e030016001c0b282e681c21b10b04400c1641c3e660f01c10303c3c0b143e54407231130301d85401c0c0182800030421500584800b42c00ba010040707901c0405003440031802213060040c0704140028160302d11 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 550901780 1250 550900530 550900541
    0x609020d0e010e160e0709080706050301081e060a05041b08150703090804060809031b0a05060a06050d0204020f040b03040c0f06052a011b21020301050d030c050a020d1113 75
    0x102100e00300300c15400c00094511350358001b000c00e020b2258401012980440130840c00005118980e580da03643d604000c40c10303041000d4921009041a810020386600000103d04681d001000700e42c005555641c60414062006500404928201055401003504100403540303ea90007002c035030180c504d0700d840070204c044800803040034106a0007070100744001489a1144c81d08005000304480c10004802c9800b42e06141d010f0205a25901c140c0c442410400c081c00340c1640103040a00c01c212692901c8003107a004450740800a10956000913020f0f1200022400e840c050480422140d84a2400d840c0c00c4202207118064500c0c00d494a285c0080e00510a40445209050b54804c070f280300340103a410210350800154980c2c0c0c040d522a44464012403410505204110180d43d424019812106000d806020f01c600c000c4c41150040006000c5511140302454419901d4600480400301900f4074604019041c0030081d840b10a505052080c40071f100c07000c00a60300c0448801030303244401d500c4101102c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 550903030 1250 550901780 550901803
    0xf090f0e07050703020c030105071e080906190e03160c0e130807020d052b110703030c05070b03130c05010c0f060c0507020406030c08062a0a030609020d0e010e 70
    0x6802600040501c1d2150300a880c80f188a40103c4200800400002e82562411148103000685044090541000440c0d400d03082c0748039420103c0d01783c24500c0c4419100e92008003c01b41c80c0254504010a0300fa5640c010164205800140e0ba141c5040d500c003000c484400d05002e03208149000c0c00031030912461a9114000c0c1c10070128a40b0b012400da55000407908240c000380d0b481018108500046a020b005501900e002c00b10000d000e000e010f0000c448140c280344588080011010300703580417100020b174103015280c040c1064401c0c95407500d41140f4144007500032003c40311010051040c0c000992400094581c44ac02401104580310001107a81410f117a034041c01040c0c5c542c010703101041c0343d0780c08103202a0091034520300d84001500802d064441540c0100c030040f00e502c10400600f0350038482c00c7d401ca1045a00ca90a00c144e43c4450101044207000d0415020000103003201c2c0740b402030f440300c1e000342500c2406544036000240032800403c0e624411040311350078102c55200d2007034041051080d44 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 550904280 1250 550903030 550903049
    0xa05010f061103120402040f050708061201060b0306190b0403050f07060f05270415050f060903030d0c020c0a0305010506240406031a04050f010303090f060e0d02130c0f090f 76
    0x300c1d520f44c103194440b03406841030341c205507a64a10310491001d4010180310f0031490b100c80d046800d00c03e090051082c206200c2080503458403105010030340c1e07082c0c02c0300d4210904441180302d21640a014880920729588507040100c030002e00002003003808a5655558a03425081d649026a200010340740c044800c051800000c0081290320076100010302114408984988540051030680d070208040b110303800710b1703106c500d46400001c00591030300250f40303c03500c03105460b12818000c402d004a9079a000b06a41401c00c43e8692100c15101d901c01c0040301c00080300108410480e61392030400600074581591140d00810038501310f40021f100c1d840183c1500394203820510314107494288101c00a010782140e4480c07040c0b03051411182c1c0d0741c071030040e24000c48450314508400e501d14074024105820b103600a08900c01000002c02c0140c1e0018140d41c5000000d9524040104840c40002c6004070344450f1240301c0e0b442c0c43e90700e0030f031564404882c0c0d071155002d4980c3d0b11540d8650000c0fa00b83e206500c6902d800 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 550905530 1250 550904280 550904287
    0x11040c11071d0423070b04240509011b0b13060c0207030201050f0c0705040501090b0319050a030305190614030f0a050703120c050304060c110d12260a05010f061103 72
    0x300c2c04d030414181506541106a801040200035605044055011080c40c040114042c4106210b072150040c0c2e000503480041018181c40d100501070f07000d0345100354188142d40d40b506a080d09411030b52002e43d5823164164403249080035014030400611941134510901c0d21014081913400010404240c0b90140c4590f428103034000f040071050b80c059103c03807040e80150309d00044c2c0b0351900d001b441c1c0030307001802e4041030160410090600d00380da10310586030300101650010010420110380340324402d40525001c00d0035075400101d0285070f03003040903006c1658a060350004910a201d81122aa03030402c905654030300c810f48a1040da80c0a40940140c800d800c100c03001c0000600c0b0820044040d0700301e0a04e41c606012039128541150800e501c800081041204010200003003c0c4c0c402c415070004a032805415480c544802c001e001d0384580c00414040249040c3c40b00c45001640412805012504900c01c0e25144581f000a04030a128421000503041c40110724540915079400009094400540c01d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 550906780 1250 550905530 550905533
    0x614040b071b240207080c010c020a0c091a060706060504060519150e030d031e05090607030504112106092a190e0f0f090705060711040c11071d04 64
    0xa0f0034507030805105003050301c00c0e08454841070b07900281580500540c040e5840c2d080d00c201079801d44100c1e0b1220b00454101c3d00e01780d00001e41d4605288191120440d0000d031041c0c100443e0000c3c140321400e610342c0150081003220401545170000310a8070002c0c0c9003880030030740e41e20510012070710071054191145541c0b00188103c44c0401c600d892000305030300e402c084401c1c1050121341010212211080040d8448800c0b0400d8034032400c440f00703240c0c03806404109501d08070442548170000a403007101010b0700e134004030b414413900f040b10650358040105401000c01d0035003a842078001345198072034860300486002501c0c1d0000803500000c03007400280c90a00700f843c80c85015501881020010394005810300d0042c0e1352002c102403403000b91a0070080b014090420030b100c516055030043c0f06c172029020b4001049080c4002299400455500340c8407a61510303400d103005041c01c4640369007160442d14211801444c0f91303006d040418080592011f60b0003042c0c45402e036140300690b140ea50600c032604440400c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 550908030 1250 550906780 550906793
    0x70c091a19060507031d22151a07030e04020408010b040f02070206091c0602070b0a1503260903060f01150c02030a0201110307050114060f010e090a02070f0614040b071b 74
    0x1103600d0711400400098010a000100100481c0110381103220305521f808028003018400c1d16510b03010203881d0030a25103045880001c1c803882d8001042480808140e4208050013001c82e4400a080280155141c58036000d159008001c400c0e1000c1c481c034144150102c104490348201d50b1015000303080325161201c51001d12919900305071119812035815a480700c0451154400380c85d80300d01c01d00c02c4031007505281045ca001e81c0c58001000390b56902424040002420108022042d41084428084105103001c040310481c044d00c3c81481d0980120400c0140d8001e0100e4035906a810754643c808101e00611822a101c500700c910082d0907a2229403440e001d0341c0607402d009407400c0740030200ca16080c115038843c0e094410150700c0030002003641e001e1204a203020b55039280d4542003071901c40e080c0f84010300002c51004014001d8070481741e000442106115440101030700550b045241440001401c01a40c02450340c2194140c0d80521050089004148114203940c41683c840b0102010220a0b031601c1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 550909280 1250 550908030 550908047
    0x9030b0c0f16050d03110a081501050c010e010902090c040f032d0c05010e040e031b12070b07090504020405090615042d08060615070c091a1906050703 66
    0x1008078003818003030445650302c4240c0c0c100c401c03407080019104000c0302c104040c0907030b8041d440c214680c01007440a541b03226804600fa590000e807000341c403804c5800801c010ba030355108540200081e94207001c10102c20305415040380711304610960780a8201d03a219184441f40c0d0145000340c03906104207010420201e207d10003103c0b540f4040c20f00c04a0742400300802a29010071401084036940310301d071020840c0c0e40e0031200051820034150340502c50420a2a810354036441004480b1800002e907030503007840410104004450b1000b0300b019599100c03100c8c10150070310a0300710b90342c90000e0b007401004111402c040c000d03181150320140040d4102e0700c400c400c010b41c1c1c812859800356a44002d10001403082880300c48201560458400c05c5044403002003d06894074054011519950100052000c1a11010010413111717201020458841d0001e10b0800c1e6910321503031003040c56904100c2c11410551021003182c2c24500c0c111a064100e100456140c51143c1300d80c402c40c0702062040c000031000c2806071420b03 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 550910530 1250 550909280 550909297
    0x414060403021c23100501060806100c05070503151f1a072612090102120423060106030f1d03030606180d03030e07080609030403030c1104110a020c0109030b0c 70
    0x260f002e64003402004e03904000711000d00c0e000c0380d0040580003c100002e1141502601491500c1d070618940f90300441d020403403814403801001034003107910040c054244452030180600074181c905280404142c020216403d035005000315400006080000344912842e4080b40c6040780d6540200c21480c40309001500301000690740c030161703404042004000d20440c44141a04101c1c0c1d151a500281601c0d200040b005103e07003000e0307204000780c40395102e131001402e504c913a0040035001110f1b01c1c3c80b180100c41064043d40c2d400b074403401c400401c0c000d41640010341e000030909820010b00559800c40c1141040d4082e9901a541081011900358100349004010b11050703c0d001c007803940e64050106040010f410415800241ea9984180d40650700380020002007080701d00610150030700909158492107a4803008080c0308502c800ba00401003004189184400000c200f008490001ca80103403055005005c8031005025040604003039602801001040d0303030b017040210004d540c0306400b00200350f1101d04c4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 550911780 1250 550910530 550910543
    0xc080f0f2113240507110f0303070501060305061e071e03110f0a03050c0423210c03070b040e13032a0204051608070305040204060f0305030414060403021c 68
    0x2d41000860b0041880051000c040c0340350301040d240c039008040f042d445080b0380030081c04109503004161100f100002210003281d00d01d1784070100c00000b13459413089000080183d400c0181c00014001c012900c10b1050117049074042082c1c41040b400d00103091704903294404a5220441d00d02c044405d80101202c0506a060010b0390036025800083c29030450307100042c05150018a4589095050013015008840541e410381003c0c14518420203400300320b0f403811211324170618405000c1d40c4e59040d80c50f1040e000340031410a2071618046070b0f281c46011001c82d010f0301c115000001e510320004221011101240c00c001c0380303a01d403000b075101031450740340c0107408100e40c0c8072200c005a510b1910042c04c3d5903811784c0900200c0401e1040c003081e103400600520301d4201c0744c43c03025000c5403c103461990122103481c00003070079912440098000c04058002c00da1085080c0404010404000028000d58071031100920b24040d09104000c8188500e000c000e40040c200b00e12541e42230050007800c094a41f1950 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 550913030 1250 550911780 550911787
    0xa242c040b0708011517040516030b090c180a0f0b0a06030905010e031305090901110406080a0b043b060108010902013203040602040e0c22030215090102030f070c080f0f21 75
    0x110024440c030b03652b4005650910000c4140003810000b0401d0b0a00060b064481d2982e003180440400b0052100074820103450b41c65485041c500071196010541c405401030095001645580008004110f52070b411a41586424041c110802002055038440003c10120440c25420882880b0b48042d01900b0150607648452a91201031807210191002c1c144d59501d40c841e500d0210050000d555100342c2182c01645044e00041070301640a6801202c1e81c90030400031040313695410700d6400114150b035200341d9405882d00110704c5272819042140158001d07a41d40007007400c440c00000c842d004030009002c44407500142210f040030b052010350351081c000d0f171005060030342e5810b81c80303541d805c1150003001e0600c00180900d03000401035000344060041c00c40740e007030043c01c44d40070802c1d0900446a1020b00c2402180c001041d070706c03c00803500c10726200704105890300214607240c042c10800f03000d000c0041c0209582002145000601c40c1c4610781c420300100b061480284040540d001c219140341040e51081 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 550914280 1250 550913030 550913053
    0x91e100b042a17010609141306060207090f05010f15200a060f02090a05011404030203030412060522030f0c08070b0a242c040b07080115170405 63
    0x7011205808200892600c000c0c003140043c41800e00003034600e05450414014060075a12103100426603040d03404e500b046248050000e8111104030030204034032401c00d000810402d50204407502152202c54083c881004d64142c1c80056400c240541666460340f441c040181111001d40c900480302d41d400c240c5103e0380d542d002c8452500004034000e500307521680c40d000400085110724500e90201d043c046046c1481203000420040c15440f54a04100c1010904180000004100c50086078010708403550341e5620700109198100400c410748075949424001007000090b040058200750300704120f10000d940319541901d0281603070316640100440540710400003115000103004d00c5009054004081c81c144c2002001d41d0081c07100041030340c46000b1101003004141204800b514107484c000901c043e18040000c01002249103c03030040b0785140c00380810300c0043c48406002d654190360740000350780c03114100c50100030009480c00c00504001c088044e654944908035030406d10400a548182465 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 550915530 1250 550914280 550914311
    0x504230d050d0f0810120201120236150307080a060f08010506031c0906081905071106060402030615030a090b1501030b030601030c1703040305010212091e100b04 71
    0x40b0741c01202050410144084594000210a41c00b80c41d0301c82c03842400b800d05110803819030407141c0090511010b01840c0b01c0a003220f030155400740500c41d42d080c9440c0001c8840e60400d8040314480c641040c0e00c010b2040090414241c0002740c4802c220050f4690f441d080390444010300b0007407440031499503580c004107102d400142c141c40204041400415035040c103104250500c00e4900111124104c0c5600f100403464010b28941c045035442e041501d15955107400c020032001c1c100005004d0a40303071038100000c0d203401902404c80241000100c0d115640e0342c2050008a100130358020340e01c1174403e07a504901d101003000031079210245200c0403540e0645e075031790811541d00c251440d0702d1320603510000d5030895a261007030107804081140284499450764440c400040068090900007003405000800d0756002007003214021035110300210f42d900710f15501501c1410059410740c103103001b002508480040e00e031904401040040014041d141c001070390f00030060a00030549504651940c0d6803002d070781c82 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 550916780 1250 550915530 550915543
    0xe060c0303011811040b07150921180e04030f1d040e191103010b03030405060a180305031c0b040e0c22050405010204060f0807020a1e02040903030e0d0504230d05 71
    0x1040081c547c41d0220303482c180c092001260000306d10185010900c0b0046100c1c4070103900000c04400180305540044070080b120950800b000c1880d800d00d80c00b0002e08407019014681c4520301036960799413410f100005c12030390040c00000d5a9079188610390303410041d18107507204020201c0d90340d0466914440354080341060380c1c108441a500241c04101807190390600703024010301040d045014529040c10500010b00a0040314421810401d40e2030301d101d24500e4105071140034540003030803661901c3c4594196031030005061440c1070000c0c10085000070314100780c003d210144007104042e141d810680301c00c0c0203030348140c100b060181c0080403540b121210000e12849001d1405100013507512400c022024080820814a0108111b40c80040103e042c0c1c1c0401c0c01003485501c010704500c00d040b08164902d0f41d170024000039601c18540401582095015404010011b803650181c03003011004c500c064070240694400d950850000d10300f0861301c03800f294500d0501c224020301d42c0070505820345030740d0328044 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 550918030 1250 550916780 550916789
    0xb07020c0a14090c0702030c03060114041b020a0314040b1606050c120121060e010c0206180304090b04271b05060a0e0f10030c0e060c030301181104 65
    0x81100e9000d40050805a2101000c0c120520040051030340c4500826000c03440280210008000410141c007190b40c240018039178a04001c04440103541c5a07048641c880342c01351005841a0b24006124050040f03c42024114100344d4010700034441d810384040d01e014000350407400d4140b10821000c0340c11088580545580e10030240c0c0c81d41d41500b1458040201c07030b00a400981306a0080c0722045401104030700c0f00741550740c22500c0d52140d044480c0600840c0030b4044000700414103003039504080c100c0c1540540d04450495003201c0017070301d401c1d180948114101540e0421a0000c000521005031a43c00450080c000544000307040181e40704030a0026202501050030805403520000910103031007041803038001c414803081c0c001d61070a000243c0c6440340c2c00112080c00650004a15a0744d9005a4a5440c0b2710181a4120500395404020000c0a400f03055a01280606e5194016400d0820035a032550100070000c1d403440e42410139042501c1c0070b0303045081455482c2c03212181d2004040010b4801030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 550919280 1250 550918030 550918033
    0x1e0515040303080114090612030c01020d0515040e100e07120503041a04080c01030c03090611040609080c0d0f0512070b070905010e0d1104061e050102011404030f080705070b0702 78
    0x12401d42c900200300c0041a40216003031031a07002d072500756139600002c142d0050350445c0d0400f08011260485402c50080902000307071540f01040d140088540c54001e20300c1444001014440061484100710880d03d411040451503446001202c01140441e0f1060042d072708014200c0d03905550b90f40c2d20480c5188080811561500013140400020f0007403c10042c01d034603203080c014113060410705400c4c2d0b1203225643e880e04141d1220b801c90a814029841403640582080c42400310607081c48130086c1c7d550052041d10005410000000340c8034101044614480b0700c001c1c40c10980740c0301a150840e54080d14441a100ea0003200f5441c1c41c2282110001e0400502c40c0b0036080c030170301d05014080c2180f03086600880c18000c0810b07101d032240d0343c1d41422404003513101e040d001408102d140032078010801b40c3c0211002c6951410141c030000c0c0082c1c905421203409078024080c84500c0c240380000b00e04280c2e0001c003c02e03015144125940e02644502e0780c421745600e0714500782909500c0d00c190552085d545900135 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 550920530 1250 550919280 550919287
    0x1060e030102160f031106070c021005121e0901090f0f0302031c0603050d110a060f0b100306080c0d0b04080705010207020a0303170702030c0d0503090307060608061806010605041e0515 81
    0x40507000200c40e00501488000760042e03142c008030250841c271703100c00e00a10403240c022000e2030441c01001139400040c1202c0070075000d843c28480d10035130020780b40761403000705180c00d0005503209014058400850b6100051010150007139859541441c951003044055000a114a503500d88401c64a0152111040d4000c20382502c0c504059052815288406042060501200d500c0000028020740041c0e880280044d02d40e0355540c400d40101101c28109a104900d40c0d17041a155a0540006041c1c9148070255494414054104181c0282010b00213200c60030000000d0042070700c0401400035a03000d4400545407000b070740d0008d4088c82d459002100881c0410100103282ca00c0140c01a47c4199070b400114036190381030102e03541e6408245564010000000300240c2512814000e0711074903940080144089622802e1958448404465414421100d80d450490b1200d0009165049030110380b03a00b03203410f0402e0003401645140c044c14800750340d02c402e0001b6582d142c20369103841490305688034544 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 550921780 1250 550920530 550920533
    0xc0607050715050c120403031407110118050d0c0f0f150b01020c011e090f061e030623220501170304051503130b01060203090a0e07020601060e030102160f 68
    0x21401c000503405050b26103041c041004010103107085079008425201e1014040c0d485140c100e024140d801585110b40615a00b40a4100e81141d0440c4514480c1d100078407160140700c04248808602006c090225440340d103c4c0a1010300455404900c00c2c010802e50000039020b88901c0c40c0d4100b41902101d9654145030031b0301a002c503a104600c0c41540074400b4000c119107150000348401021442c41c0042128609210403087c02421000000c00c01120500010395803920040d0245404900340c05a0048005070311f03481c40d2003441600f0603141e04144001d0004221600c902280110703c9079070b500710280341c1a404444064620104d9800b4000d0b23030100709503042100c0401501522200d10009600601050280c2d40c2d400c0d4041c080c4502240001e03450759150348090b21880301c0001c2c050491101e4000116160b40c0c040010a200481500c1c0304036400d0f900d545412a6a208035901c0005802c24401440300e207224052400000c20005d0025040c151590406081e45503132920844100000303608400 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 550923030 1250 550921780 550921793
    0x90712050322350d17060a12080c060105061303080a0c05030c060426090603060303220807050a0303230904020a0323040c0b091314070206010b03060112110c06070507 73
    0xc0e1203d0040082c29201d88203030b402401346403010810300f09124128000503a1622280000380040000200f42d200c07032880b0b4100507006034460041d940560040e5000420503003061000c645000340d03000e50181c0035501c0e41d11030701d00315001070140700d00b003001e2194040d010540410152810100e8000940301c03500705031601091070f51b005002c09070b900000308002c0038940054001d03104141d109481071036070381e900d00340083d003988500f604090146420765a80c0d41c0e8801400302c128260703120b07a402c0301c02040d207074010004090a180300044c002130000b9000d10380074065042d1400011490981d00e410150820002000d0307800c0b84c1072440000c1da1342c0e41ea00244002180703034a800e4007004c1c81d0004107800d140d00d0307000f01001107000b4407a10b810000b039508400c1e140c0c07450303403281c10001b56020810b0502854442e0001e180070303141e400041c45050008101c0000f941c04aa014040586900800c02161700d202ca016091518203485411000e0009954804082c01036a1140840ea61886e9a0f82650b25120 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 550924280 1250 550923030 550923119
    0x702030c0d110d080406060509010e01140102060f070c0314030a021c1506050a1209113c010201240611030f07140c0301060905090712050322 62
    0x30104054080b41a050300c0002c10b8902c0d041c902d516103c04190b40d10b00b03120340900340c50b60109412074004000000c03402d2507203070440d05803082034070072103031205064004903650102922014130f0791000d003010513176542c00380003140c40180c42410000703000400040c0c592041d800488e4011502e42d000101d140d003030002d40741e80100514414070200080820b45114808180e82d038082c5006006002a080c2c28090140d001d03000750b509049030074480c0c8a400d01c8c02240f0001c601c1e9007075002e4036000e07005c0036045180724030140c1804a03014059048403c040100203c008002070400c1c103555848204d0801850515448c600900c8104440550300d4078014000308058100da141c0d0800d42c0003400303942c80d110102e100712601117400c8001c5101810fa00c1440b80c0c241400d00340020760545c41d04034001500000394010760704c0ba9407020141c5140a5840c00c0f01c16003042d281d040100759401c10413180a08078580305c0459403400ca0340f9007090140b034681140390780d0180c2d0300d403500030700000750201c4251915000214 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 550925530 1250 550924280 550924303
    0x1210614100f1217041a0d0b01030e0c27090d0207051f030c050d05040b041b050f060d2d0c030e030315040209030d080406051e07050c070e0702030c 65
    0x42c4003440e20700880e0662600d021140184605502c8400e90148420310098401404081c80c1a11400300b001d405000e03207500c000c1300c0040240c14401005490341c002e1003140700032061040584107030254030703041100003100c0302c035544602e04800400f074810611080001d4031909000b0000d1061f0b07158560080e02c2c4c03c140d90b1005118140110280388000301015003002c203020b45090100341c03002048c40c1a50903015040d0020f240c1c610301700401c01880001c1041c5c44c0251b0180500f0724200d20190401c01c0c030301c10603000c1c480e00714040510680c7d080c1000c2004007410820140700152031001d12414441c000200c1002100022400301c0455030280948104138a00e2403e0030100040318400f1506500e0b030100402041e880b290802000209407565011a10400001400c0d0750709070b990703004c01520342c48050320250b40480c5000000381402044202d51400c007503680c400f0144554070341104a0722a40050300110007030103010030000d042c21720507010303601848144e0055070b1500c0301404414a081680020b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 550926780 1250 550925530 550925549
    0xf05222909130305040e22150c02030406090506030a061212080a0204030201080f060a1505042d0b160f0f060f050c030a0c050f0705030a0f0201140121061410 69
    0x9002e40080e40007801c07a002c0f40c00400d00d145413a0f80b0b0169280510b40000590a00d60b103840150381c0400861203100d00090f55155020440002980c00c12a0b49010354091180890a00481446545041c601843c0c1c4100b1040001c2040c0b07442e080d14034440701c02444100c074043c2000140c180c0c0140c100c00360642c80350000108600381403460f0002860400003030400d4051384181d0000c10007580303885000350b004c2d1003602101c181c3d415220a00401a5101c0d105180c1c80c401000100880720006254a0f80b200780c5581010300c940b42403d1401066a01000800102c111640200350020760f0055026020300e0107000380d038100c42043d09101c025034110340b880700c04480c07078002003040c2643d0840c00c1d03035000040c04100082c5150280e078295002d20612015a00482c0041041d03803c00c44004000c046e20001a40c1d2807600008c000702c04d80c240c442100b1040080c0168800501424803691900310001c054035403100310075203403a00d500c4215051400c43e164000111400c000382102040f180b100107180342c42 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 550928030 1250 550926780 550926811
    0x2090f0f150414071e090b040605161209031709030703110f0d0c0302190807060f03180b0103060606050403171809010603060602070f05222909 63
    0x40c03100c4000340001c050401c40c40141c000000561107950010038048654058110a030a000c8009052038890901c15074603c0d840c880411411841100440212210580c2050410b030401d0415191900030780d40d00300803442103030f01c0c68020401c0750051040720907603901c500c50518118113255001c1c00e4448190162400d0070840c8030704903200056101c0450f074000e513031346c1c0c0d07491240c5001030400358ac07219485500605e004884e0081c0541c0d180700c04122442220f20084da240b955a2a44e681e560f03511a0441175048200200a2240115102c0c00fa45540d40380006110b05075007031415200303482c1c9105580e03006100c401441040042c0c8541c03406081182400c41c1000d241d40e46458040382a01000d01605001181500317401080c1d42c103040003001c0092846a070303076071942c40090084c225489410010b20035a400041d400340408140000c0d190302a11203044c42c050103c0c0180c180310a1255020216601d8903509044203e00003024540310340c0d41841c0065820394410041d1200002d40b07a460054442e0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 550929280 1250 550928030 550928041
    0xf0d0b04140d0c0506190608010e0102030a0506010801063f090c06031a0d05010204170f151302011d04050a0b01170f1603060510111506060a030b0310021602090f 71
    0xc0d5581e4000391b05072030002010071800c16400542010760084181d5030a000b0a0019880107401562003000060000c1000e951510300440e502c0e0400c0c4503440200b01031a0950114a4822070600030008407604965201210b20031100d044544125070321001d2640c0710020020000c0411074a40240550302d02400101070940c1c2c95140980286900d42c070540380c00d0b06510402400390184c50051003100b000c560381241c00c2c000181c68080313400c0810018042e250100c1c0300521513100007801118800d032800c40296050307006484032503072466070000e180201c121440740b6641b02e004040c49041100d2001c50710000e494005003c84151424402c1392400140800a50f215030300d940d04c5d40030000340d80241c0f041901d003000b03600808032900a0b5401095100c0c0d0415001d0700404460540041001101e1140600c040f6503040f81c031058803865030010040010780d001350300c40d41049082203801029101d141302c0c20801c030f60807680f101c15440c05001101016209626241d4034503a4030203d410444115440c00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 550930530 1250 550929280 550929283
    0x415110a03141803010204090510090501060807030221010b0406030f110f13030b070818010c0206180f0f0604110d051504080706021615020901050301050f0d0b04140d0c05 75
    0x80e840b16080e880d0301040c80394002e02084260310003020094021513845d52500c41240180000700c0b40c4409282140c040010303816141d01c50503048540c00d035203141d5103866000b4110042d520050030240c0440342d1540c020183d8000101c1c5500a10006015555581c54400043d00f665100d18151812615144d0303810401076038102203c00c40800d1089940c3d650301c15216080f485282d07604003800380c20001c8108044650018480f9005001401180301d4041d0100c103031742d0030f03208803540220058101c20045250030907811011722402071014281d9a82c10b01d0968014a00001030108070f50a520250030b000600c40040c204d142180c4060741e094800740305a8071026034411100401001c4e000d038940002d0140480d100079030780c440750710290555480289088010070503601c40019204101c078180c1d00c044000203442110546c0130180c4400c1d08503072070300c410002162010a034550f0010705140303070180010909109030748a10302c03170b502882e151079074588070074500b000803810f10f03050200c40204078001c100d0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 550931780 1250 550930530 550930547
    0xf39031318020408031c0b060f090411040909061d0609030304121806021b1e040b060c010c120e030f07060f060902160615030c290415110a03 62
    0x9940c10216030794120340900c028403c40d8003404082c0004120003101c48560200304c9150113400a060045c5e0b183c3c4020404c40c1d04c1000c0349036403400c40801041d5a981020707004050703a00400c188140c00d1a41c0d589044d407c1e50341c100707400c40e01165a4070a6071182035807281c1e00407091150038000d09440c40c140c6030083c0e8a1202a01c0546200e036403000c4440c40c0c03449144c2e0b61501130610622a81078913520341c000b9683e21500c140c0c1482ca1a0328941c2c0d01e00900700350800d0005424042180100800680e0901004001d902c1081c2c0d0010320801141c8050002402079258461040e0b403501d450400c5d254502045581981070b480c201d030400c10244440c103003030105031411250003550021f6039803c07645484e0010701d0a43e100c00c0300d00b4000b054440720715001c40540d10700280038603018492000c2e881d04d40c0302e00030030500000b04900780e00341d030520009066410b800308000d5442e01c100424950034113a040940c1203540440c1508a060b01030000c8203038403101da0314154500000401d0031110507a406031480300c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 550933030 1250 550931780 550931789
    0x901140105070308130f0b01060807020d080c0706090209150a060306030f060c033b06061810120804090b0d1208090304030206030a0506270402060f390313 68
    0x2420101040680c82c045d950303c10356960100390b0582d031a12925040c20407100c240300c1d03100401d0b41750000860341400410f462001d40d015698006980d5540d04a40205804c01c5405581250b43c0d0340c100c00c016103071000e40310b010711006016404440f23079144c2040800300854210504141c2499030410020f501c00017003204160340f065000c5000b00000b5021002000c02d480300260503401c005040400f4081802503403841402905010418101c59050b142d56010595400d40c00c14003041d40c19a44c6080d4140c0f094200c0d1000807202d00160b942da60012000031000e10680ba0729500040400c580b00d581e00c01c07007078504003c1c5c946a04190007601c601c0c0300326815080070b00a011f00040080c4d80d0310030600465000d161300420040c2c4a0419a1450b801000704445680c000c040642803640d000611841d03070b1845410840c01d9048694540c0d00b070081540222002226034078040c440b021420700007480801c03240790010f488108001d8051a4000c2c5440000e0000783d46400410427680039038001c950700c00566 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 550934280 1250 550933030 550933037
    0x301090e070f0e150d0b180a0312090c050307090608070e15150c0d02060f0906040c0603020d0906090501090302011a0f150706051303180e01090c0c05190209011401050703 75
    0x2030341c2c1c83c0320030420200380d081e419134005ca2031110f880422916259171402003a010759102c2d881102c212000b580c4011001c40540810340f4043c64480201d2290400d106d214410070b03c036a00d280d81c500c0071138507006454100202c495111070062146803010001180101008259030788070307040000240c403554005407641c03405040910219810800303240d04480c04400040c048030031940c0c001900070348170072081e00c01102d510207480c00f054034070b5400100c65001d6904a041c105a0918003c01034000313600c0b0144a0142948400c1d459011a8851081c95941030040c1d002045035a59444c0090848540031a00e012070b402d00074100c41d040c2c49a02680d0403101c0242c40e11080303020710900500b024052900000d2041d4109070411500c038030b041c1c184003411403181e15000e400708038910031034042c0040d034000c2012501c050801003041d81225042030b00c6010090820038000c840544820707041054282d008221034a04c002d100c800c60902d5205070f401407201342d52882d600b8012500013800ca10a440b80903080 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 550935530 1250 550934280 550934309
    0x2e1107030e0301060e130519110d05120708030403170c18190807240c031b051b010207090b0a060c020a090207030909050603030921210301090e070f 65
    0x1500c09512150183c16400c0c400030941c5840c00c807101d440005124201c03282c1c0101c08000b900c0d403442e40c040c03810305c5520400310862107400278203000d182d121540090b034042c400c20701d42c804242034200c01842c40c3d83c09049840c1e9a480c05040260950650710684501e040010040110303000815040d070741c994200215405030f01409000103a00f0240c0001a0301ca5040858000280580d00060040441d23901c00500ca8002604808900000000d841d41601088102c806080024412641c50b00341020b94461160050038a855039840c041c44c183d101409203d040d01c04910940c3c0410860f001800c201b081405101005004500340340301d81d220706014010b0181d08403003155240c04100001d4800d0f00811512403a1314180100b049485118804410307180801251007400e000c02140c610354805080c1c003a512030080c440c4002808200c5020819009401c9840c081c0c40aa00b24101490500c100c000d4495040c158080125130203a2448029a07100c070008100442d04000c007071048500f040300a045 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 550936780 1250 550935530 550935557
    0x130201081b0f04080a12080c0904090204090f1a0c0408030f030a0612240207051f0f0e251d07020c10050a0e1516050f2e110703 56
    0x8600840300702c52800500440c0104102c0c40004241801c50b0041c182c10f08507011441094600300400c3c0c61003250780c2020480d54040b41420340108a545101800000300c0c103e4a44413000c0240003418101c80d1404c2e1503080500a540d81c100b4107801c580600c0c034040c649450319800d40c1d9203126021040c0751100021000030003c1b111548080002c000c0401404c100725064070308800752a54014400c60740201107001344140b03551a200340d80c04994000024088405070004200503c10400200b4a005844003009000b88a05000d0b05458a0010b001020f8801c172112040040040008e1460f40c0c0c0305010408021841c0600c50407001491242d010340c120340c82d00710080307082c04d06191038030390048070001140800d0b40d401001840c800355550399094800c0022002c0110031460070395251090359041c08000541c450441c0460a0144504225502401002403181c141040c22a59a1404007480c0d0080c5a162041c4042c1c00707113107035450041041e610b14420100c9503004242003d4100b1011401810 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 550938030 1250 550936780 550936831
    0xb060703031a090106110712122f0102090f0402030c03040b0408040302040603140d141813060e160e090106120f0501180c0201020412020f0d0804060302090913020108 73
    0x40030282c0980a00c41d41d60b1600c1001e80b00c640381b442c8882051150ba03030000356218035481c5a2410641c40500901c007003544072000c6030444400381c0e60540409070624200143d40e0004400c0080c04008000503866122030b604000711040701c1d900e03e074000c41c0108100171400304010100c95026500a0407502c0300e403640c4c200722145000da40c0000350171629114010082c40900ba01a542d0701c0d01d200116036500b000200225030002c040e102c15613615405208201080a03a40e200100c07905c40900000020355854841c131069843c140d10000c07201528400780901d4003411101600700d8581801e0622541e24a40045201608144121b20410601d1100108994003d4000e224105442d56080c030095031036103481104a4802d2108062081c61301c00a403100b1030041c0251001c60b018540c6020090450340c0921110003d200d5240d40c2c00306480540b040041e0f030b00e10142000e802d4542d00140c031041644144003800380d000d41180f01c14036910821000503030340550400e612401580785058094020880c40 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 550939280 1250 550938030 550938071
    0x201021c05180a0506010e01050d0203100c0c0c0e1b03010803030a0504021519020d0c0c0b0f0c0a0c0504150b180102011821080f010603110904020d050a0f0b06070303 73
    0x410050007007408040604c035000800704e058811100608041340d80c7c501c100b04a10061010094264000754444902c1850b40d40c8080014241400d0140010485039102c04050380c40350020101000107400340105e041020f900700794440000c0b06000e2440d4103214406a0303901004102040c03940d03c030380000d000c6481320b648010003040100c601d16240e110388080e00d040c400d909000400144111030143c0000c038410030101100390b401004c2c103200d050610501851580c0080307c2e10806c00700400041d00540f404002114000b802407500a80343c80c100010401640e40d03412034107403800107151041c17118240c48403c803185060303c00701240000c81c9120060f07015000e46031240000030304005400c0148001d02c1100c1c00300c0d41c0207214220750000ba0b1941541c10804c10f0703032910f400300048401440164000d45c4804000c03440c0c1d4000605250b0031800080036640703c84521202c1030340356030601c080507149004141105203044820310134280d0800214103907028040f00a020143c8906842040100c5600e01 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 550940530 1250 550939280 550939321
    0x5210702130c21020909060f0f0d170a02030414011805010f0e100521071e02011401091a0312031321020a050714061e09030d020c030d0201021c05 64
    0x2129500d060f40c0c5490080d0407116145003d4501000081e00c589020b91643e1480d0728010f01d44070b0300a9960003840103d813100201120b0001c040c0c0d540c0a140041c142c050004a940c40d4021942c96080205030802040b850350844c0c14050a80c169507244448650180141c03502881c000100726201d400c01c444a1040d001034640144040a10f19529584400148a00001d14000b89100700c002e4004c0ba049160403942c200001d210881800c4a000220302503001000ca10301c00071801c40f20414090340c2144080c0d000703204007561b61043c404102001d003505c1c1030a05c2d00305c02811295840c1000c280d1503102c01400c0810310102d00107180300b08a10100044406020152589682e0f0241072000e541c58100720003d45151140c1c043c00280780701c0040d00c1c0b60702d212026142505207096911007031200a03645000d514180814881024161020030030b56800c0c1e030071680107000000001c014541850b9448040c0c10443e40100b040d2040281d450700030000030010380c00c000030b280c0d032009500514200301c6042e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 550941780 1250 550940530 550940567
    0x90b150315012d050f0d0c030501261209061209070521100203070302070f0809010e030d050a030b010c0204140601110115050d0305070b0a020903060a020306030a0303050a0b060705210702130c 84
    0x180647c22130392560001d410398075541d006460300700d200c05c003140c881010824612625401201420032208c0d0117000f070000c0c0d590240c00f0504080d110020003010400072241c03002180c0c00b4203020885c901e00900321203060400748032030f030b07a058810760100394440d90f01112003422280c0000124403824402c0e41101d464981045012100540614000c0066404548882d0005088004084992802289200031704042c1d889a0385081c041c21815009494805940c88c140503002d49100013607200c0340211740e8521a0340c00c80c0b0060380360620002d4110010b030190070303610342e03d8800010304215032940c01c6400d44000315240c60704124a031504480134400c81600070650035543e010310800041ca5005040741d10710071000d817151907403101c40c1e1408a003c12201242d0540c4000610004240681c0c400f54210148090124110841401081c2568400c801c211216031103072588049845180d03028400c1481004000c0e45010079540004100030b0302ca880940465903288400110540228040c2050800404 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 550943030 1250 550941780 550941791
    0x19030908010c09090c09080d180506160318060e2211040305121201090506030a0204021c0b0f0d03120f090609050114070801090b150315012d050f0d 65
    0x42c008048803403512900095030704002045003528016a484000d850405004140304081c0803411074040c0783c00c43c8a0303041c2c5510314202003429115800281442440c0b030b1b900c141ba509852800400800c4c1c2945000500002d05606011040d8008440c500c0a8001c488020380c000881c120704001404000080e010603180188401030881e19001510480c0e00500540b07000024031490700c10307640301c5c5100303a1450361a01c1c001401030130000d40c4510f401001c082c00b11100708100f5408142240e0221b240d11401c601d050107998661a254091680540000d644c0840d038400d00001107a070311134540c0d0340142400084410001c0c4007280d40d02015501e5100001032004407040d0502600138281903000f56240d500b44004d8150b40002500c020b070042803544d40d0803445a28210098008003000b00f80180c2c8500c0b60144d030301e412155280614014211401080d82401603680094280401980750410310714451100c00220901c2d020750401c1c4a003582482070703449094212810544c031603504a00f00c81460301c1c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 550944280 1250 550943030 550943051
    0x62d060c210c02120102070c0e07021501080105060a1703030f13061104050411120c0c07030204020403060509010513031d0a0e16030b030721030c02150a03110702031903090801 77
    0x141040c983e0094850442c12414515282d00740e10920402411041000d0820000110400e81142e44003c292041e01c103030700b4404c2001000f89200783e02c0450960745440c00e01c40756282003000031000b0200e9400e020f0b05414100c40e4961a0b02001f08400815041540003440c00100c0840c90b0400c02c1d480303e002c0088440074111003074036800c64001d8501540c070b003828140910910004413054445100c0b2091241da941c00012a42ca41c0805400c5c590b030302a9a00000c0141c07541d002400203140701d01c00c0410a860995581400c4820042003101c0b0450b86407001000300e40c000c11860019016030100403505074002000c40c103498810f071310500c4404070600812203030601c80e0515105a160507a02407004a1884040503034802c9607005400000b012400c16028455a100448000c80c0c443d003000800f001e01600000c0d9181080c1e4940b242c4003030000f072036032040d95061103600315124190005500340178041c0c011a90301c481107043c04103840e00501d1701005250042c03003030b600101035010090155404c035 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 550945530 1250 550944280 550944287
    0xc07020a031412071a040822051302071e0507180c0305010501020d0f2609030703140f030f1305010c0215010830090d06062d060c21 58
    0x70340c00341c40b15500a6615000c5050315403000c40e0000ca402c800500c180f55070b001e07190078003002c003d442182c241408000c1701901302d48a803040c81d50000051045d000891801c07080c0080303a01414224400c95204100c0440040c0d01700d800a038848000503e00d030180b088615125140c9000d642005c158a03800b4903c00e151700e02c40e074103c000c02880550f020311a5981c0e99005980c0c4100b04055500866102c0da80b4070400c0380314031074103108415250b0269170b1141107a14122144001075a00407601e400025081d000d00da001050114180c02c110707121442e00c81d00c0500c8020a010282c42000010a1600810101200c0c030340d10710720701a04080200141e25039040003075540c490081c43c4002c590021400024640300100c0d841e10b00e131500c0803100700414541110818101c00c0300d038510254800900c5150240e449290072044018800d140000700203040c1203880c0204020120b00c0c07013039203c0d002900030f606202034100e842158041c1c00c140d00d03043ca0a143c1800b198a074004240740b1550742449907942d1550 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 550946780 1250 550945530 550945553
    0x4030e130903120c0509060a0c060c050c0f0f060a020714161d15040b12030a08040b0606071505060a17030a2616120f0608011b020a0b0c07020a03 64
    0x100e03071503a14610b010240c2c0c1a05135100c154000300410024400d8076414100031006100340c83c40341c0303400781a5104981c2e642003141d05861030240001c6003c00c005a50440800c111141c0184100c001c02150095056603651014000c000416454001c01e0560400860302050500f01a815050350b0041d082d1702c00ca51300d01c180610910a144820066103260404a141d500b03005200301c0c0d0b41c40c19500500300034070010380020342040740c202130304441c040024038090024201c0c021055991030445c1c2001c1c03c192000c2d40f0054010740c8554020010000000e9842407621048040703044081125915940081c1240da880d620441013402401d0071030b040508040001c0c5000001510b40c0341a030105c0090120312100204000300003141d640b000304080480711800b480151505c0e10b40101c1c9180135268132070031f44003400221110140c6540061181c1c203002c0c0201090040070312413889a8410a0000a546040d1504044e20542d140d502281140e80b0f100c048401a079006000543e21694902e400c02c04002c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 550948030 1250 550946780 550946783
    0x27070804021c02010206040809060702060a0f0306171c03060801090609050706030902010c080309010603080a031a01081003061503050a1412030f06010e0102010b03010f0921140304030e1309 83
    0xc019020085008030b40030103201142d8045e8010869a0f440d42d607140d06a60104000d250f20140070701c0044016600e1400902c040d5119640e980c2e0020480b850150948007185c008006001c2c0901001c2300400703000400d02401e01e10803080c1100d54519400550080c0701e030790001400d0394202403c10040c015550012100c951003102190b130440e5680074200c00b1107965000090024901c00150004184034401070350b001641b5a000084403940d135900c0e041c141d4488103000010944035a4240d100304121808840440320a003002040e51800d0a00342140b0f0703260380030041c1302d02e55070702c070045213000104c07118405558044203c82c2e8640c0c0508004064502c1020030315803910401c0c40010002a2040c01d49020304440c5108034915221400156800b0f16841034440c11990b8400300b00c20140d40134010602c98000c041000920041542441c1c240f800b0380d8204404111200c4002240c500d47c0450300c1980c3c40040500586c07661a00e14045031400155050381da8007000c10002c0d0300030f900180d4003c14410717 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 550949280 1250 550948030 550948039
    0x306040b03060c0901111c050d0b0904030804020f040b1f020106030b0a021b0307030f050c0c04150503010614030d08090f1506131802040f061805010509100e062707080402 75
    0x520002e00d190344280c51807122090480c16820310b0907c07402040034180c0c58a4403140440e00c10001404500303103030340c101d500742c0c00a000c14007440154240481c0049030801c080d1424820500500c011540d42c9240540c801c1302e90702c181051120043c801e500c0030001c2c3d0350111001c0340d83d003455800c1c040030790080c880f007926100f01900089032001000003160307032159050301da030507100c03c80c0c1009071000d410007403036a0000d000d240c49150140d5102c0c401d90418219028402c0131441c1004141030850303039103030001001a091410002e088d0b54001411082a180918010510303684402d493303418609450b012070040c0c4074801200d89c01c2c40300c0300e502e45c5c85054150741c4107942c0d64084507445e05071020b038241c00c0703541410710314000c015040035000584d0300402200d000c5106951075880c40452000c180402802c42d5a60005202500d0550003254108580080102050703091032101d01e1f0070000581210310652608030b001e01d600c5001c0120080320350300f1503091a02840c01c020090100707801110100d00c80c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 550950530 1250 550949280 550949297
    0x603010c090e06060315040c0f12021e030421080420090f061903060203010f24050a020c042405010206091b0612040321200306040b03060c0901 63
    0x81a00c5000c005080b40c10700d81840d011034481d802132060760307440030b80f0016444603060703003440480c1c55038020540300c00c1c1e1543d25003071884130601740180210615200001428010032070120341c281646090b400c0c0c0111040e4455403501d82c1d1900c1c0300004000b0a41d01000c2c036215036001c02d1070340c0042c5407a200300d00900001802c404100e201c0c201c020016403809610020040c00306000303400c8001003a51000c1c01400340d60183c001800c00700070341c4920f0b500c00c8a1550b00040107105901984401c1001001c00c1e1107200303518140c10b42080b0402c41030f41d100ca0104480032900e0301002c2e100700540186002d014004011301024809480b51410481406c1c0c0400c0d0728000001815505c00101c8501c20311891015041214080c890344203000f46c0400e4040d4045018003040c2110310740c1240c258010342c1b00303450f0305040c0403501002c100320204094914480c14904201d000030040c0c031903041d07500c60303030f000300c00035581d9403518009001012140140c0e030301342c030840040008a0344254010001c000d000d032210180c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 550951780 1250 550950530 550950551
    0x303131e08061e06010e031009050115050d03140403021309050f0d080106031d01050a060602060106090509010504020a050d050403050309010b0603150616060e160611060601050c07030807050303060301 88
    0x30756000554168044990040742c0551284103c3d5165400c1601403515013040300342400020302c0c11401e15168080556280f4640081101c01d10400154460071400c80840e5442e0100281c4203150b000405402d212480c0c0b08407601000070b1045402460b402020607203409000504000207200040e002c640c82d200e01c04032000302c100002104003c03500e07070360746003409a03081c10b00072000340c0703500c282032102e15600b526050001242070007950b2040c0408040041c0142c54800002c0c54040b041e0311240030f000c1c24a0042c0300300d44610b04a1415600c06880260740c0d0000d06000701d450307200c2c400c1c10540b21444c000501c010142d12000540c040c5508900900c1945000d80421071948020341d02480b180518540d03002142c10a01c002d000b0070508001c41e40060704841c2c461000785c4a00b01f1500d88190003240d2444818501e401e0400d000c0c090034500800c071506820380c41960b0391005480c5a05000000c1209240107004004600246034480000b907140c2200b403a0a959940065078201d00c80c2d402d0010112 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 550953030 1250 550951780 550951783
    0x20010f0b0a080c0a05041d0f0115060807020a0818030307050a0c0614040510110a030e100815040f0209060a020c0f09090607030c0201021b100e0706120b0303131e08 72
    0x400341e840007403a13110f070700e45004200001040c4850074070040680d240c00d440f005003014050b40f83d80301c00810020500e4005a00000c25654140d081031003071025680501c44040e030300080583da07555221044c540d5440f06800044044501a80d00f268507110015400c0100600070400303002d500d10414095043c90b80302c3c1015034031100a1a110020b05909002c100480c0c035114865220400c2e00303007003400b4801c1c2c3e411482d80c11720480c001c0c15030110740c014180364400e0604000a00944030249845080da0030301010f402c4221044ca0f40c2507109a49800900d41070305485c2c0c1c12107000c400024025580d8140001c0040d403140103003090144104045c00018941c1d050000725103118800c000040c005a60b1074280c158014081040040115917080c4941c1c070901d40b84200541c1032424110040c40703400080072001c403d40c1c5005100c03400b15080341e01d04100c29500304a8942c040c009030340c0302050101858010a00d140a544886d40c0c1c47c03d2201e10002d00190b4880c0441d202d10100010b5070754441c4c8803072425 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 550954280 1250 550953030 550953043
    0x30f0f05090d08030a090828080c03010312110303010609210809210d05030406050601030924230103120201020906070201030906090b010801051f0b03010620010f0b0a08 74
    0x5034000402d01c401e01c2c0060002c400075a88152403810014050341103445030021074001e04a006014900d02c00000d9281202d05c0262400100350300e8140141c3c901702105480ca800103110040028004011140308503000e44104250507050b501101e03229039656200a20100d103910807808841d848a0001da000440c11080483c0c80d40c100400b603107040364640c10710511034050001c01c5100c070449032001d24558001c1c4211118414176581d4983c4a040c42d0610308100c41000c0d1281d81030615204000780000c108828801041c81c600364030b100a0f001c0a01d4100143c40c0120702c540c0c3c100440c5410028201481da0000d050720b004005c1c000448038049016400c03841048045644098180055401517110783c000301d00f518819a00402c0120241c6da54080d004020782150045944440800950031040f483d46600342c3c1030b40c090700f09141d180c170140404500c011300482d010400280602140b1070480e41080440c5810702e0300800c002c0c2c5d410785502004141c0c0d000118481c81e00d00e5800985d94400081e02c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 550955530 1250 550954280 550954297
    0x21c02071719080c07030c1d0a0203090d0e03030d050906010611160b0315091005120d0c0b220f02091005060306010c0204061518061407120207030807030f0f05 70
    0x480341d90300b400b901d6030003141d0042a11401340b445001c1c408400a81000200d00040031040032600300e0b076090321300d0750705600401840206100c0c418410456440d40c00a441d0741074080c10708013070721101c1003807011906511880c00500c2101d0300304410f00c040b40b080010320504940582c0d0314401c5c500403450300c1c562203407246105a504060129824040442d48000658121079940090300c1660104030126020010441d5000b042c0c000404040040b8200640303248601c08441c000b030020114000005000070030101d8018000007564400a0114103103d00d4903000c40044000c10a60b081840c905582c030310502c10710403030145400300c0214000b0040d11248605a440c01001c0904607a03841c001110181040b40042c5e0384151100c6d80004e894100103041c0d039540005640e40c4030050361a40211701c03810300d82d80c0a901007110540007811500404070695011641c41031005519946500080745804090780000e480704000049600030103801000032411100952145040342d11007000a031440c1c020b0b10907 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 550956780 1250 550955530 550955563
    0xe011d011a04050d05030c010b0102071203031806050c0403030e030724090f140f030a020d08070807061b0e01080114010302220603060302120304030c050907021c020717 74
    0x5010701203003905410651030500d2602420143c2e900300060049070740c1241038800e134000080c5283c00c1c40080c0100b101e520020700092222a00c1c025030000044412440502015525401403c180c04180100701e801c1e43c10010078011070820040e107281c60b038094030048002c40c0a030950017006060101e410340c201c3e2045003d001c900741400d40c088003c9282071455204100c035285010076240c00486d0000040c0040b1032075180e03444211000d0080103202001c940b84290300c01c9001100683e40c02010000301548000c1031500c42e081e9181001007401130203c010100e604001c821002d210001c81501c100d11019a107100c40c850700040151545c1000780109203c1d01403620002e0a1940241c0040c0f0169610710041000c1c3c00b80c80303d005940103804e0708031f040000d0701c0d20010008d61910645107034103102d0725000345190030325541e260ba07072030b11941c8101030240310703107a000486a6009120f0700000410050001030a0400440001d403207400382d0140401c84401ea41130781a44201c005564162501480c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 550958030 1250 550956780 550956839
    0x90109090f120507021201060503120403080f2203050109061404050601090216061a01031d06070f030b0915030607030606082205120a120506010f11100e070e01 70
    0x403030384120b140380070300d0800a00404000c41c200580720400d2410080d01810000200281403004150414a0301c0142110f20002488280049440141220346080e1101c0302a40c0e2049d030002145a41e854403001181d050151903400414020f0642160310410b2250f1007c0280c00090641e41200d0314040d2405405940400018485001d03698001c00c88291034100354040c500305540c1c1c01d010740c0c8080404a582403194a080b409550b003601504a0b841e8040300500540c29400b10342950320800200a4810844081c4040d021709002c3c3d4001d030204207024050009030b2401018105040c0100d881d124001e10900700000c400034840d1042005444550360f44d0310b80354558501414101c28487c19819140004d2203400000034000c00074503402c08901c407983c54480d0798100e0301034100d018230360002d44040e04020801c50660792100d102803a500c030342d0a243d000411102500da01e0301c4c0003483d09500b103c0c50b1a030401d110260020381c903800c43d62481e031150030030380e214100309403660100d1411412007080390 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 550959280 1250 550958030 550958033
    0xe0906070e2211131d1509040803040303020d0c030e0c0303040f03020603060a080d08071d060714101a15040303090509091c0806190e01061101060510030605090109090f 74
    0x6410040c40e20365814443d0741844020003103021103002541c4100c1109401c200700d81c0040001a98442d0302030600d0604a2000030001c5c0420001c0c14004d00050008200000043c1003500980c10303262240303580d9004000003030f140c02001d401048114240b00483c45600c0340140e075071078008211000d80703200040c1d070103045195030b0a22004be0400342c43d00c5c6d4014543c07070005c900c9003810010f4035060001079440b0290390034418800b400c1c1b05560701984201c041442c9082240f521070104403905290f000c861031480ba0721080c4501c2c1803d001050b07944031b0a040c80c900c4d880304042c03000403104554084540900c4074260a400c01082e12541c880200414140e9908010310300c0d140705410b6100c1a280141c0740502c5824050307021445418404034003140e01c00f4144030a50810440a454007a1940c5910f1603507400c103440f1402a10052040004101d000000c1d400251030a410a000803d000b802d0f48187c40e640810240260419002d43e50040848100004500000307010305000640c10018102060040d0b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 550960530 1250 550959280 550959349
    0x110d020c0d02010311031e010f1202090703090f0521040810110d020f04140103181103160e160c030c03050a0903021c0606090228090e0906070e 63
    0x301e00080e41403556828102e00c0f030b0107420004602c1400c030304541201c0704221444103241283e040e08814540c1d1114071083c00701d5220409020240c50f0100c3d40d8100640d00c0031411405003190741802000039400c451102e04102002607400c0b0149201820420445174085094455006903c910b0409504c1796900b042410515800348299400c5440400e19008142c042c072010380c0d10040d51514102d9000808100b6051361782d0086025840c01d00c0c0510052100e000016012a0f1090b0b010f466650684901d500f01d5400704200d109204001d020485031980c0e505007181400c208481c00780c548450b4018101d6984d00c105030f15041c1960507101c2d80d000c540181c500700c900d500014041420302c00101ea001c000360b40d99100d501050b6007203c00e52085c810300b500d004402e50360f441d0701030801075005000c20325a0f0040c0320040c0300a0306243c82a42c0010328000b01c22102c82841d9400003c03a1541c1e001444070054011504d0b40c82b420203a20350710703c0c600350768043c40a03200c11107034117000204488404e540c0c60400c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 550961780 1250 550960530 550960549
    0x40e0c06092403060a090506010e0103240603020903010e06010b07290109020c211c1803050304060b090c1209070302040c0504030b0c0f03060904140616110d020c 71
    0x4000c0d00e4210781486001c0440329103008900b003102c60141c080100000791a2540b201c00c0900b030620710501c0346c2d040100019000500c00503106040c10346611401d01401c0e00c8141404c0340364401c81c60241600c1d51070320080c1c000d622407001a4041d500340306c049068000c0c0014028100c6415001c00341c5083c141d511050b00c0603081e140601c80a001301000b6024140c1080c14260203001210300c0184d482c40c5003061945810001410b40c081103400c0001d01d1803808299068901d0000002d100c081c0c84800d00803160001c01d1a1b40d510090068510100002d050703100380510700ca244200d000b0410b500d00302d0108526030f8001c643c0080720502c2042000060070401c015141c101d07850b0000c4904250300c81d800141661759101103c0005800807038200240402d4060050f08001d80e00031040c0b40c5218410b21200d5844020682801010000041820400070341d151440d4010b085d8103aa0840c100002e01481e1200c11800c94000070300c410756258807100001c9828031100c106900203200405080051122141 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 550963030 1250 550961780 550961797
    0xc030219080105150102010c110601050d0213050408040513060311012a030f0e0402030c07020d03231b01020a021506031203010b0901200a0305160f0b04020f040e0c06 73
    0x800c1031001034185001d024560042021140c1640c0713507840c04c00020b084550f003504030400c1100e0740c845c02c001c1100114441c0e054810075500d04141901c01c0c004180002200c1c06004422481c0508000c103000d41c01c0054002c0d03c1007243e045040c0d5202c41d180400356030382c0e4000904529250010700c513041d8042c0038990400034a444c81740254a0101c001a030321181a80819004994410f203400841c070350000c0c4038900350f001114114258200528024824025031400a00a154507542c5006044c0250b0520200e8095484580c0c04480c19180205d640c2e008140c1c0e9022141c4600407800c400c4506001341c580720038140e4010309581300b51414408200e1400307080503401d03001d07000490203041041c000860103099074900e0f4aa03924020000100020001016002080c54640c1d841d10386107008501c0f0b085480d09071230102d49a20701000016090081c0610007006c1c400c1d450402c0b4200b125441d400c5200340c2c022104d51a90b030b890390082c03009949850040c000c0e560081d40f9809100d15110b0050220039 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 550964280 1250 550963030 550963069
    0x402030a060b030901090311070b0f0a020c130e160e060d06180503070c36060b1b0c0906130f090515090609031e03090c1909060b070c0302 61
    0x16914510718507558000e6130385078501c1c1d445440d04410701d50896400b0009800d04001000500d11b01b4145000c14012030401464200e400200303406014070800c8a100b246070001c0441c100c10b20701c404604020020300d841c07180c290080703c044045c2d03503007048614003c0303a2032460040c8403540c405040210f824100301088503076540e10440440c4500e010315104410500c12401540d507041581400c40c00494079502c5440c0c2051200ca400d02c1c2e18082d103612880c0305980500c00312480c1d440c009018013074091504400e24a1f4000304400c507192450301c2004c4680d482410560b201d901c040b8081c4521400211503e81c1c0000c42c142004940e0081d0703521002e500d10102100088c0c603540395542a041058848c0d10000442618050010040f0107000c0c00f500601500c00841c80e040302c8843c0265651038203003600320174590100000e104c0b0720b4144400007408000038100d0226802c091011642003040e402950529440d1110101e44121110102c0d89540e40046d480b2011600d941d08010340003151404080c0103 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 550965530 1250 550964280 550964291
    0x30106121e020403020910030809060703030605090c031611070611100e010c08071e0c031e02030a0e030705031005100e190b06090919020f04120c0b04140402030a 71
    0x15041070700603034851005020056034551441c01081800c90010300f580319420100c241c2040000c040d80c08640c0313030920030381d0141d466080c00d080640040525901c01030300030074001c1c1084001d02c50040214421000300440410107403440c0c00840c0c01c2180000c8458082c1e0041a060003210301904000690f840034100b190000d618030540f10303003666219461021245e450380001c3d00015008941203500040c1460400b0001c0780c500d501222034819001c0b080180480c0e41c41031002d143c80740204402c4400e0541d81c080c240c00d01038600a56940c804800034001035100c580201c054500414200101e5900400034090708160404503402403070080c096000d035280f0306000041e08601e028081e44101400911183c912002205c444155030f40c409410307106940400600d0b1182d41c400c101d454100d800401c814101150741c2d2200ca0091040c4d10040c0006d00c0041000900c9556040024544500c20301c150140d00d9510040310030f05000d28010381040035000a040800390070694003070765001c0789048e80410b4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 550966780 1250 550965530 550965551
    0x60712050a061e0f0e0c09270f01030308090705220e0a15050a2c0f07090e070909050615010905040609020901030506150f09061210081b0603010612 65
    0x280325484100032a0800d80c083c1000141ca8500d02070006203108004280303140352007402c071000b505c41c4585161140b11045003031800f15141c20118100381c80000204045030800399804513035030780e0900c0114001a6240300055402e039011603200c085034000740514241c400d0354852441e10031001c20b015040c0507072f58a000c0355500c0703003001810010741c0201c41d150f890b07411101a14065a4008060f0312901c0c0c100104c0c808040450a11080903141110600111840c10280076003800548660b10710944107116000c030743d41c800303944040c100d940e400081b901d41d0380da40d16100080e45d48810300070700f4541140b80014240c240d890038140e19181c0500d0b0441c02c2c140c848000408135405900702800c416404541e000c0c3c1075030507106150f040700e130489016090071b80220a85150303110f00d0b51201e840c5071022500c5200c2c0c1d03c078902a0b64500360b020141c080780e440c08103014080600d076407058404038462840c0780800c44618144600040d000544914516030031724005840c0c3c0b048400c407408480340c1da8400c218 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 550968030 1250 550966780 550966799
    0x5030c09250512010e1915031407050a090e030a0f0909020301090204080606012c061204062c0703020607050f0f030406030606050408070614071203050a0e060712050a06 74
    0x82400e10759894803a107a8110342004066080141c002d140d0340e03c1020140040c010041183c5070343c108401c030000c00c0c21400c2c00f5405411181c2580005e03c500c0800c1c0099810b66400f160300c2007505d0041e220702c1c0380695152118410344850542c101419042000440c4500303101e5200c0d000035800b50b05000344115500d0f641503040307900036070080d02540da001c2420700008034103102194000c8001d2038910040003005066244282034940c2e200403070114510380720300e82c1d10b42200340c9040f042c94180310303503484ca420f0034000082c2400d8111418800c0ba80a0390784100840304c40700b8220304c00c840c8014403100d82141d00b40016a400101e00743c61912820030041f415010070401c00d1900c1c120381c80595251403074820043c0c02e07507480e07410031402d0290034401032240480024407081160b1052038242c00c02410300c04480140e114424014003801601010000307020f40541100f03024001d44442000b40f014106520380d00c4040541c1e112001804c448004c10329410160007107038000881020020300c00d1795804070071 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 550969280 1250 550968030 550968091
    0x4140a0f0506151008070f020a050f01091a1b031306020c0a05060a0e03030f0c04030803070215010906050603060f1201180c210f0618080d0f0605030c09 67
    0x1140c0710b51140c810440c580d45494424841c940301540c0303800404848201c0a880e138040284080c0822200000b0019864420060300420b1504901a02e02a0501ca01a03601070301902d00b0a5440000702810350a8507020891014800d204580f29503000400c2240c01103100e9002034900001e58a4100c2a000402d000c0c0c030090240000b014001e1641c441107181c010b0516100410000c1220300d00403030221418004421a0750184c200a07103201282e445201d45581750045420140042a011040064064000861603140c805000002c0010782e81d0f05400d1080d14644d004180c0c01c85024000724481c0d040042c2140cc004400600703816041d100346140c1030849884113160342c03405801c00e480d071090210b00e040300c80180aa4030412812620b101102c01c1280a98200091034140b00000410500101e513000f1781748084c18903c680c10310006424414a141c00c5403050001003480c20f03a0032000c03120300b8881c0740101c550180241140c0e0701c4480411a0002e001000c103402d1000c000c00701854442d407000807 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 550970530 1250 550969280 550969283
    0x9060a030504020102150f040203070503030a1704021f080a0b2407060f0513110603060114030705070b010f181407030b060f04300f06021b060109020405030d0206060904140a0f 77
    0x240c60071f51800380109851f203440c6911484c02030300208510b484069215450600001c4036107404072442e200c5102040200060304021a00010060284520703c0d901c90107a5001e0100380c1010b1048010750020001006a0a0b60000c60441d02d600d50000c03685100f0040d05003207009020010b00603480c04c2000c02988c40495020560b0004050084c081250b011055459202c080c0d0364a070442c905000040c0018806d05011700940c680070001401503442002122195175224801c030440c0d59540040c400b81030302c1030145000300c002c0e001101c010041315208008803901002503112040d12504001d17030042c040188615001803040051035015011f2400a1005180d40c1e00106695800c0c1e43e15585030b01d5004181e03031027183e1702ca514170003c60b01030f0b03030034120154014100595030f00c080307480442616004006500c0e68080c482c000148074060754050011600240d0039240d00d2207000c64126101e0700104d030320543c0017200b01c01140c0801c950302840007203102d8540c1250752140303150300c032810707604a8940d0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 550971780 1250 550970530 550970551
    0x515100201051009111e0f0c0a121d040b010e1c0b0903070c05010f030f1b08090316060b01020f1204140103060518220501060e070509060a03050402010215 68
    0x2e1103c0c10280043d0400108100c100400c00401c19450a030341c581b141562076101101812201c0d40d0b00c01c1344030f0480b030484c03100c01901541c910214203e981c0b00c02d030004080d20000d80d400350010700c603400b4081c04151507406030000700f0b85804130300800c0000d10310740d0a0f0504114010301c180101d0744401004c0314030f00b0800700302030001c44070501d4894034800f0010b05201c10340d00288a400c00082480c05007100744c46090a0050442ca901d0380110000e0800d4218116558203102e1501c2d03c0042511046150602595514409990b0032044640d00d2040c10710040000441140d0140400d251760b100352503104051050f074820610600340c0e03a14200034001ca40c0006100000d04000c09074030307141a00070040080c02d081c0900d0340740c6000604103c069441d904003424003500011100078590f440100d2006940405c03110550560030080e000b011140501011044610041103280e40110141d60588400800f140d20b0040c110304210b0107050040c004034150310400c0550b21440d101d07400f00034841c3c501481d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 550973030 1250 550971780 550971791
    0x1050a0506010309022d0402041412030901020d0e06070b0c13080109020d2402160b0a0e03030c2215080703090215160210020f1b01120515100201 64
    0xa026804440024014038180341c500318480300140c842d02c803400044001521030300c01101d800070100750500d4210103041d41c454400140815844451880041500c0c021340348040806142503001e90b8911a40c904180542c3c0030210b6010010f201d0340107144254405071045041c40d0040d6901c140c0e00b203003520b840c6200c20000c01e800710410240812400144000c00c000c2c400b80e9810740208400c15540e00380903010030002041f4070010303451101c81c0d602c03a00c952a411944d078400e02a031030040700032114007190706c1020700020400c400c1c004d0203018071074000a0055461610380d0500703e82254400500350034407003103025814411351b640f142c1580060039001074075030604140c044000c00c0810014460000d052401c0000005a1250011200007840000700b0540d00e0522880c107480c202c080b40402940401c99468005c141d542c0400c200a8940040c2c04850602540c50090135075509144910350004513410300c125042c07039042d082150000c00c0c02880030349146078440802d80f0030f0710011560707000d80c1d1200e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 550974280 1250 550973030 550973041
    0xd090f060c020d05040608010611032809080a15180b01121403132603131d04030c0305030403111e06010f05010e0d1118071b03121d07080105 62
    0x18022440d032a030040c60585c0c40c05d820040050984001070145800b001803a01c0701c107070219030810898107240120100142c3d5482c2d8040c4040b4a03a20112101c40000d41d202c1c00003ca902d00061001303ca5644060480b0014102801c000000d05807118500302607107a1200242c0032502e41802c0d10b000c0c0408441141019000e4200714201002d04550b400745507104001c074401c0c00401000e41804e4401e40c0c08030f14007010003041d0240740c2c9411000742441c40e00001910b0b0809510b22007069040360603000d806001608400a011010b9600300d4010f0081082d542c40c41001074824001994060311a0411b40d0401d010f80340f8481c58141140042c1e0340801d400d50b2072250070003082000c907004210360a1240d030124100000200302d82c1001d10b090b401560400110010030011403410180910040c01c07940540350403458a1880305401d40766040840d560f07194208030508000c3c07042e41c03519010740740d9401000780707549400000d0411489083c1900856208040d000380280300e000d0003052442d00200c0c6c02c1c10302 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 550975530 1250 550974280 550974283
    0x40b0a0b010f020c0f0a08010c0e120c0102031b0703060603030206040c0f080d0c1109101401050306150c0a0501050703092307030b190207080d050a200d090f060c02 72
    0x10030034506002442c4200c1404540c00030314030054441c1501e42c1c0c0000c03211800454000552600700c0503007035090121522225a2124900d20000340854031122000003100318a86c4031180c1f0381c0d4850040c2c004001d80c0e101e50b4038442840100c8100e0501322045941ea940b502e1040703481d2500200c0040c0c001506020a002509003150080c0038072000b1001c03054035101000d55141c01c0034521009101080395031405001c0c44451503500814058009021450112100c25022440703000d49400c604110070b40b400d00f5403041c811340784034034005044500072491f10440b1007125001100030904a108184220740020000e001d014015502501c000c074070300d4240c1c0751404943c80300c03103070348a80340f030a0303030200e6021398400106102125080340c00c3c040d854a40e03148614880c862041c0b103400a500004040042120701e600610041d00408000c1009448207c954800c0e0f80a0500c9860003480d503405285a41d40018011302218008100024801c05540d4480480d10480c0000b540c190340e5a0549a41d000d80 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 550976780 1250 550975530 550975541
    0x3030e09060306072007080601060507120f02030a120222140319030f021e0a2d0816021203040905061206040605040f0209390319060b03040b0a 63
    0x114081d04441c42e05060040c8031488080f8038070145ca45103284403200c0041848000098964081626140d43e1141e5000d005680b000d181260714640780303400100d49a01c140e00f040c14018041d4061450002c07170900859000c0c4641c8400205198201b04802a07015103581c0c20680c1c02074007084282c01464403410405052070381c0ea04d40e011380c00100c5640310f62242d1040043e002036060810103094150304404070314018a142d410075070402482c040344849140090600d890070301c074441204e80d00314198000800001d0002540398804101000c81002403110405004041c1440144400c8003541c1d400148900a580070385120b40d400014062100074517500609500250a07502c001182030365100103560355500600c05007600d40d9441c042002c020024010300b5000350010151041e078108010113405003510101c003e4540c3e000c059451240c6000c0003281c0584c0d18500010a003103a0300e6200703986a50307000044030a5240e5aa00010490301280c1c2c01840c0980c2c006c000c1c0001074908201d64070b003100c1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 550978030 1250 550976780 550976791
    0x82d0a0f0204031505040c231e09040f0302010e0a06060807060507030c0b06060906030a020c01060f06170c040b19030b0619030b010c2003071d06121603030e09 70
    0x24010881071000ca400c081812001131411040020195254241101c071181d0340e400c8482c03a43c0f1150741c400026101e40b1a450305824084030b19004070080c0c04aa0201042c84804041e0440780c9400014080307180c01e85100802ca009000104848000c008400d0401030881d0301290742d9aa00d00c004c4c0a60f03002000707a5800307810b4038200b082c07409030141c601500382c0c09030010007814001d0100020301aa1201c000b503d00800d005000707541c0b00c2c00c1104282020f50051300e1240c80079840c103000001d90302c8540f0b010904580740e40c0c50300d85000100d03551280f01d80384010400500300c03000b0000050200c43e520000d10810200300c403401c00d40e4040701402029661480c005600c00d04090258199415555003100320402041c1400194601807a005980001c01d20070f010f00400035000c0200c00c0403c0c0c000401c40000307402c906640e011034542c015165000d0140004442c0090303101d000580038140b001105994409100484440e1100d0f9803400c0794120442d08114001200454041c16504110559135000f4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 550979280 1250 550978030 550978061
    0x28170c03090601030813090c0323040b06040902010e030f030a120209030316060f14090706110c0f010203070c1409070e031002090105091225030c0501082d0a 69
    0x14144105a0750380d600c010700000d03040c0340780040c0740c80b00300d05641103c0004021800040c0815a4141c4029004205440c000b1310340c200140c0ca042100011034011510841c1e02c080704e604a612180140401080230b440201c0c107229032030030110000d54013000b81040b030b803001e400116501d090800000b0101008000b18401e82801400076540d55603011003a602043d0300300c2e00c4542c03c01a20700300704015105541d2001c1490303251581c500d00ea0424203140c1440340c101c01d011034842c655180030440d20280403940400c442d80104110810610780111151507150701403044908002454885201c498016401a00c0c070420851400c82141082c0ca0099841300481c00e00c00c030b140041c1d101003a2100f402c00410011154001f89549040e07024405841c14100054024801c4424a6050301d9031180b041c15811030701c81c40b088404498032030a101d090266035000304000d815030318040040da015000030300450298510650444c06034480340000e80e1076031405200d044820709041c2150011034641c0403480218 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 550980530 1250 550979280 550979287
    0x30406090203160312080a0b0d03030b09011e0504020c0708120c0610121704091d07050f0310200304050a1104110a0e030a06060602061e01050d060228170c 68
    0x1043c4440f491040141840c00c100d08640c1e05d080ca40c200411032520019800102c849c60701c000c1c5035069001e5070082c40309840c0942c0310398030780341050740079001c1d648900b60445a0a400b1b2050b070070103030003500312102e45404540746582c4802c03020341413003010282501c075660041081075864004100054201c0c1300c80b84003107600340c02e002c4c0c0310f40b500740078210280c0051030176a1590103918441007198000d0959410400440d180603e04607036181c842d030500d42c0c4038803d080001c80c0c20715015560061032007000f402420950310b2418044080c10021140b8400491010700c860a13106042c40210f1042c0d1081028004105036031520308070410380c403000c0078022845c0a4071080b121000038211a41e01c9001d080032a440c03840000000e16101a0001c000c100c039040c01030000e0f03003039000246180182074036105001c02d202c40c06010710b1110024401c0c141d01040022005001c00c990b81e00030101404885c0080342e20081440900c014904014203000004040340e2015a155444100c201d41001c00140f50a01c0e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 550981780 1250 550980530 550980533
    0x120f06060d0903020c0907020d02060f0c07020d240204090c11030307110a0f06140a1a1e15180603130311100f0510050909070b1e0304060902031603 65
    0x854001c60420540311503481c01684203042c02004030102c0b804006000d10b0f0b10345001032009445020301c1e07090902501c51100414082605080910b1183d0f0401c04040e05207015502000905a6600005d46405100d0042e00541000414440360486180200503036514903020820b03085030700e100f14200411000d603211030240038010080341c0e00120300d171514883c0c10018046035400c1170300502008041060441015040027440c0d00b00c40032800c00a0040c840039501c0003203040656945003200d40401807000d000c00001c0c508400710b080504c0354550000854000c000108280801c00da1500b01b00110104403510050381c0d14021108840040e40c41505504140741e902c400300029007401001e002c031000700b0f5840317000304011003410103036010410302021800c010034100030310b1b064a0101e188201841c01003071500f06540c070140504400401004181d2808041900303c3c3c200303800045211003180e01030b80e9240e401101941c041d600524000a0540309441050f1900d100542030f030051b0142c010b000c00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 550983030 1250 550981780 550981789
    0x5070b061e04020309010e060a0b0a06090b0703050a03060506120a0605011b06050615040e01050a2304110d0e070f0806010e0a02030702010b0405010b0d0e010b0d24060605120f06 78
    0x42207015240582c0700c0d11140b1681c1e0140c414101d25980d0740c822101002030740f080c140c12401101c84252901003081d0340369641241d1008481c0101389045030104045400a88214001c01007044e20349000503a2548840010f1202c0d4440c442c1c1c543d4203100d420910010220501ca00c00003072809017080c0400c0210100203e003842800f0764080c04142d0b840000400d5a180c80c80c031000d140c410740140035030790707511020400c03144d003028080d003409517210301e034040344540104004070100482403803106080c028030030030040034203c5280c001541040c1400310050203602802280400c85103500500103003070500b280d500f03501e181d962003451958004001004000c001201741904a00003070b00c0540d0366500c03541c0981c05040320f0240c0d560028a818000650380400b00c0103401001c0d1501c100340590441d49000e903084e6810080302c00ea120b1440d1500c607000078404c0801d44e1000d020b142e139240d00f901c4400c6c0008120b486603440304010400000380a0200c0c0101085154020007001c142d441d00d081250224 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 550984280 1250 550983030 550983079
    0x4031106070c08161b0e01081222030c170609010c1b0c0518091005011a0702040f020d020705070f080307060b120a03020c0f01031802090c0c01060605070b06 69
    0x15015100000c3d4410542180c1d9040342c0845030065034440e860a003500485005005910848800000010000c125410b01090b00704d003508461140b9801e00c2b0b00c820605a00400b5080084c210341c4522100100041201395104001c10040300386e10001034500c0105800c00c5030041c480d02e02c0364948641c11440d81e07080f010007400c520508203294200030f44c61400521500c1150400386d4450341050010303c604c944a41d0310b0b031080c0c0a0f041500c03102401d444421041e10420300500703810005221107101c001c40c0c2200640311144c0000d00105007543c420089004036030040032028840c58001503c45d05220f003c2220030000e01d123010b90f0803445890200c2c280c0c0c480c003e44a004095948071811203480342c3c5d0f00d40c0ba80c2d00300300c0d50303505852503a04207180c042d40e1496142d00040c05071034600700c4020250b00920468000c895407039041c0c040c0d44c0159082081c020402480e0400414050020544c0c1580074030944019100940390130303644280314203014081104c01880184210844080013442d1559407659 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 550985530 1250 550984280 550984283
    0x10f15060c0c03170c070806040c060c05060f090c0d0501060807081c140c0f0c0f1504030f030504122f0d39090b06030106051206041107030804031106070c 68
    0x10340030b88100800341c0c804907210b10404820b40713106e01e03240483da803803000c14914055840340031127542d1a60b071164107644000c0e50f2200900350f90000c0000544005131214450750048518044d580020244000100b940c122041c095685030354600060011540802508015000690082640c003107124103600c606803c95241400304403d000c2d104000030f2503041941c184a9005081c1d441000800301003d66074032004960510806090300c0b103008070f04106500aa0440c0c0802c400c5203850304507155410700702500601103080000800000902e90498003051403000c0c440c2c0e1102e280d00d1080b8050810247d11029a070b08a800b5408039001d043e5205a401940300e94018200311640310f82e80c01602d00c487c0482d415011031090a108007081d002541d6601c0192181c3c4201005160384280500110340001d00500300411020440401c921414110103a0b004100820220700b82c1c1c200d1009403074503003101108602003484403081c0010160048c0404559219040003013107586803e800c014a041d201140 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 550986780 1250 550985530 550985543
    0x201110301031e060c080901050c0a0905190e0421020601120f030903053a0801030b0c0c030a050306030c01020d021c020f01050709030b0a18060f0e010f15060c0c03 72
    0x3190480403c41682d4090322941016082061483c0114040c01c1d4100480b65411694038000004400c08101401d85001d04811740c0c0d4404e480741003109000405d00403500b5500c8619003140d0000711000d0250f88103206910440f0300140034120b640c40d80c18a005071030010000d5400110050060a07030081d92015120740116460003c20f8403803c068031340508640000c1c00300e000e558030021b440d0340d000c1d100300f5103040154001d59004003206200140108403100403030001c2e01600041000c5a0b805d00040d8011984051151926003a0600345255500c03510021000c91404403c100c0186400e208807072802c40d080c00541100303081d00304000d440d541c07550b00f030040145501680360107291007040610741300030055008010b54207280740c0142180c04244070032904082550f00056400f806406040b44035007000d102c490280186640c0c80c40500000c036054100195034050745080301000b40904c0e0f019800740c03080050341420380c46180d00c1d903034010342020742071041014000001403c80310074501165003011 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 550988030 1250 550986780 550986803
    0x90a060903020d020f180f34050c1e010c111c080a0b030a050601080d020d022d01050a05090105060103020412260406020f16050303071502040b04090b0f01020111030103 74
    0xa1111040e0000c100180031b0305408000500d14141501340c0035903a0f035003a021640c2080c03c086144039401c0740b08500000003120b540e000241c001c802030220802d4142c00ea80e60010f002010344013010f03105036030042c079a464070341d4035000c1a007200601d60984d404070050420342c01039014007002c00c110b800c10103080101407000202c492195170302a0940600040c2603e450940c24280251fa46d0b03028042c3c17240901a03001c40c8100c003800000e400141c8140ca4001e480c040c0010943c10354401c4900484c00c441000c0c0b144855112003081c45541e201d403411035030005540c1024112142101c00050030b0070305042c8104424424825010f018000ea280d0154919940315405014200d0380c404d46841c00398281d90110300400e8003500460b42d0100384959030304840e802462035a006428040394032680390150402c001c9840440d4006051510701880d00101502c1c245d40c0f0500c40e1075590040d80240b11207039560360a1815442c1c140314240c04010244001c0c40550450041000c0030b10040c0f00050007212540d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 550989280 1250 550988030 550988059
    0x102032d0c0706140a0f0e060c1006140103021e0903240a20090906030a05030703020f0c0a03080a03020c1204080708011b1e020f030304030e120607020d0f0c020a0308090a060903020d02 81
    0x421540400e06840a441d0008548031101000c1d040501034242c2003080c80d0540455375219200b590003640d4030f00080d24100700000504c103429403000103071744c0c0c0602486820340c072252103480079198003c4c00d41103a5070755031802203030800c01c0351225020070303002c141015264070781580d5000c1694151303c001c13034040300103485800c002840c10b541321340010040c0c040407400310189038010523040d1020002c035040c1c4000d12090020040000d03914000104885010700100b806d052181d40600032144002c0c08490820060100d120015040785c5c0c0551510b40c4614010301003a01c003070280317900645100b43c100c40c2242c00f0100151860b1306082c9020200c00741d050440c008244204001c0c02000c1c00c42041c1d136a642400e0038010454002ca44406001c2d036030b0920070000100001400344d118101a6014019114014104541d1003030081c4280040200607604080581c0c1c44c01002c10055108002c03542e0344a2980043c01464001c1e47c0c40142481310305082080942c4656005452042c0d040300d0712540d0a424 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 550990530 1250 550989280 550989289
    0x50d03200a050d060609031a0c0f0307020118150f0203090604060e162c04021e0307030b0c0c070e070e060a0302040905040609140a020102032d0c0706140a0f0e 70
    0x48003c0c0540040c00d0a00001da6142c0142414080da800f61603240041d50f100d44410440c05001c0e0350031003034000100301d9075114109100c05160410224400414041d100111000c070107120300b00196081e020740300381e40c0c500d60018414101d448409840c294250318007690601d40f1340728010009440d180d26032080d01160b003c01c0c010420217451024400f064140c56401212500a00485056804020b8030460301d64070440010030b840340da4001c00d422504c007000c014681c0c01001e400c00f0f0300d8051040b510044002452036a402d40b00f64404e0103e191038400320205145001e00c0ca52000c83d8006000c800d219016900000c400c3d105041942c9040e5201d483d2482100280320b194420000a131411080c40100000358021842182c0150020202c102c1c071000307a1900c43c041440000c2c0035030310422a40c410000085800c02441c1d0600002200c0c40b411011100348541c403a550f0085240c0000c8000d00c00300d0742042502070b0b940c044103107503400c0407a07026000c0e0a1013030f001e40c07039014404815203500043d0348 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 550991780 1250 550990530 550990537
    0x10e0703093504060807020d032705010e03040803030f06010f0207030b15060a030c08060f06120a0204030212070801110310093303050c1206060904052404050d03200a05 74
    0x61607060f03540710340e124001082c020f0113455100c01401000a44220244280902801d500000d100c1800056001c08504000d11603d107045425548400400560070402e101030b000900000024559030300c0c21001c0100e5031500140480e051080000f8030188041e4001111000e40f5404107801d5407548942070202050b1045161565103c940001c0703070302e1202c2d41500800e20b0034000d40c45200454450804001403124100301c0c581d040239007031010340310482c144458245c014802280052825850780c02040d03036191404e0205086500507001000554024411001d0000f0850071044c25420302c2c4241003505480da2040c0151552641d625540d16003407841c05441c070b050780e0a083c14100201300008012030b03030a44411ba030280a9a00e00c0180350600804030f41c56000d003175010b8806640e45a08010b9603034405031007610644503548000c0d004420340207230301ca45280104481d0502d46803d1400d285424411990142058109440542d002d41d603407000e5000000e01659060f25170300d803050300300c46501 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 550993030 1250 550991780 550991873
    0x406050d02040801050112121d010513050612060a06020a02010507032607031b030204050a05040e0a08070c050f03010b030c1c050715020106081501030605040c031208010e070309 78
    0x518200000484141d5a520403c0682c800d440d000d11100f14000c05803006144845050100e401e03016889e01c66600c280000c011007182d850b0310f400840d807070750045211a00700b21491684002d1841c14055207207070000e240c1004107240c3c8003c054040d03407076000801a0007641002020710040c64505e81d404600003400c982d918002c22044901131402008c01000b508001081104e036440100011911901c240215010b0780e201034a007000746841c12092000a0080410b030204071300407040440e001903d054018010a402031409401c41400c207010030403030405a00010348668584850f4000c1502e021410401c4004204c038941e1b001c101002540070320001e034010007845409190300210310910079415500c541c104030350081040540b120a00390b51999120354070402c00380c3d40c0c0700400004140307030401c1e030b800340c41100d00b0400e0580e01c0d910380c8042e4a0009444012401c0b841c014400c0001980000b03900c10b066240910016003d0740f40c04229509070003220400344000000c400ca0103503440c0c204201c41 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 550994280 1250 550993030 550993033
    0x4060512010b041503050601151407060e060f07081302030304150201020d0b090112080c030d020c01201801081b041212020d1e0c020909030901090f03080406050d020408 74
    0x31100284481e0003010703098400e0b0700c110716088415408060b0342007078000b501d0740300004207601e9003095092102c401c1e0200d1000c041201c1c1c10000d064294100c1c0c00303068050720950340805e4080c0000d500c20f0030f10701d0041c803498034004400c0400c43c4c550761012519400c05c24070b2655640305105800441d04521660300008a24205002c8820800303a0540c01888c80514008007004600801c40410110032401e204a500c18070fa15041c1101190300900205280e0952404a0f071500031402180e10580e0400c850424a60755560030304988649400c0200750541c01054610340360800040e24a0f103800300719210300f810090200005505518608452002c007041800019180e1f03030b84005d000c151002c02a0100c0328407803049030510a082c000226404c4541a5494442c400c00d4032400a103003034581800c3e810704105020000c6030244e26035403052800b0701e201310055660b038018980090400e20701640310b0a251780d81c1a608201240c0c1e240300741c0d816a0b00302d142403541d0300403410390400a409a41c00103190ba = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 550995530 1250 550994280 550994299
    0x5041e0b16020406090902010c02060a020703020a061215032004230108150f010302090c07020a0e06270103080a0c0615150503070903030503071116080c0607080702040209040605 78
    0x1080c901c10309404018400c4400303100480d203450240d01980c05040000307001c030388588161001443c005000d408004082d20482da01c40c0d999070000348400742164400000300b140c9030700705200d0b00164007030160310042801c484031040c0c3c40c560782c050450940c3d40500740302d000d1452400e00d8170382d01e0b074108000003585003201507000910409250240310081c49201d140f4070505031489403000107003410a104880d103c520804680c41c1da001d100c1440001440522702100c01c000500060390b4024216014055030882100309107071540511800301250b58000c41c68103038024410f0702c5000507808003819a40c3c80480203403201014281610400f049040051005080603500c00d0f0f01000d503003030ba100300c0700c50110588401c9600c850596140c44140c500800084494000b800428024401150013580b80d24100e100c080126244608101e840e5000360131300ca4164008200c1254200a101041c14003121841d20740340269544103440d1268000c0203003ea43c000c12040341569480c4e100b0030041c100039091808 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 550996780 1250 550995530 550995547
    0x2090a08030a02211c0612030c0b010803070b0a0f2007060606050c061b1b0a1104140112020a05060a030b13110d090f0f05160603050705041e0b 63
    0x1140e810010442c0014401c1141030041ca92465840c00c91001c00c20b03900603d071400380000c22880440d00101d0381a459140c1c84000b44056014044800090203540c500c04484081c1c0380400300c0c410181e00c0024554018040d200101c0e0b00d22203456000b101685000402c00003003004078010303041e42090300340b0518003918a00502c152000040252900c94a0200011034442c82c003503945000d4030003880ca8039444400010b51441c2d4102c110b0500036410100b0350300f005440702a02c207100000e041d104409410007400001000400907044880b1072007110103002d88070380f1390441c09100704140f18004501405040301030664071001006400b81c40090702150751000e04c07000250140401c08881c41c040da03840880da00810400f4803d0111044403801d045107403019181165000d0040d5450944424a400c1c0b10ba8000400c2543e2055a05100700050108000c41c880504d18141d80c0703503c800305050805c420003e242e64420708581c1503880341c2c511140d098808801c0c108540025030003030b809580000a5022 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 550998030 1250 550996780 550996783
    0xd09210c0302150316031104141302030114040501081b010f1107031a06030d022a0310090b0a140c030a150b0405030f120301050f0d05060403260403080a0203070302090a08 75
    0x14411700c0c021a1800c905c00f40e1a1088040754031401c1000700c0c1c80003c1c403081c89070045000c00ca00c4a040003e0080d9040c4440003042c804a1340207a1045004000000c2103009504141c0030703190050182c2c50140040385070041c1d5084a4815080310350341040031916060900c2402030420b10451102a411100b403591285440203044260300400101d455650340000e402d4a0300144229001c5c040380c0c064400300841d80080c0440c48032540c0e500c1928580428500d02a49040190f80b10301c40c0c101501082800940c00c2c0700c104003170041d05030b0074800d0900034407400c6c44e0440b13205143c0000243c0c49041d9203a540c00b2014004100e44854400446081c0e000096200d1031135014100b6611304900b514455070700b00500b10b580c0e81e84000c0c1c40354910020f0004120600c2c00440b4a42004005080750f41d01d4541540c1ea982031407000c407401c60101d05885259880452504540104200e240c0329101e00f60600d40c40107854410700419403e402900000062010340c0f01360141d0b40c44e0600944110205600c450b00207 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 550999280 1250 550998030 550998037
    0x605070f030b0316090c0c0f0b040b010501050304050a03120e19050715090504051b0a020d090b0304032f07030c051810030f032f0d09210c030215 64
    0x100007402d155288046160120b015420503e0503407001800900d080e1030344029290801c0d001c001d010890105402080104604d5641e043c032460210700103203001d00c0c000103c040186c02803410085c0c00d20810001940000c0e10490043d01400c0400d1074682240700d5201a209030b55103035011f80121030341d42c8686400d4411401155110f01e041e6030b0b40903124400062000e500d03200f20720020350700042c00c101c80d00b4103600054214810714003400810418941c0d41d441603100300d9000005038800d654200055921a01c0c0d2405440d5107030801c0d26504103501e004100610724411b40b801c03140f01c500e007000441104a03500d4800500441030b40e0055659023001c1058082e24482c0f02d015a00412181c0318400420740c42c1d602c00c03601c0b0302900d000d190454513000c40380d403807165084048c0109005038030360b03201040d03200100540503800071100700c01c44030030072178140102c1884c44018425941414130440301042c100c440c0200c04800c044411103114200690801d5003944040d40141d140c0c01d0f48aa100c6415004 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 551000530 1250 550999280 550999307
    0x901030605010f0507110609030703030906031113051c0c1502010506030601081e100f0606030f0b061605030d020c24010b031603140703061401050702060403020616060507 75
    0x100556541e0304015034801c03040402520000d04100081000228412494804042c02800140c100090003012918101d1540c00950100d10040310802a081d81802030302880c0514010503414140a120079004042d241d0180600c0f4030041207180107200400312480d410704d500445078601d1a42d4401d5564003500035525070a0040d42841c0000d04071b400d0003c0c03032034100c030102402055a0301018084030004280301c154090207024000020040307088601901ca01c3c1c5541c0c0320005281490000064115400d0380214441d031414000100c00e207a03181b00c00d540b0424500708200c802507059160250540c07244e007002c100d19601c0419001c6e082d01000071a00c00e000c10f1020814003051014010003c00082441184c60900c02040024040340b25240001b0180e28281404101000222070b101c044c000211703020000240d0b260000c000015000d10040c4441c0000c0c00e0461070040d0680110b5614442c50001070301845001800c400030200f03180c040722086400000c200300c6410140002440c0074001000e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 551001780 1250 551000530 551000537
    0xb0c2101050117010e070509120a1217100608060a0513060303110a080703180e040b1006180b091f030203100b04121b05060f040e090607090b090319080901 68
    0x381244504010110714142c2c3d0141740101a590b4a12404407900d6001c0b00419030091035408281a2800c0100200d42c0703241d1007000341c05024880340e140100280802607552098180c404103000c02c0071010400842506d00c1c52070701103625550f60010445038031260b031215400040416806151559680c41a01624402e60742d956040300321902042c0d50704003103940a02139120170025440024000d00e402968460300c50340c181781265882e01d0008030351a04079410365583c0480320400040c481202d070400080c10403420064100c006c40f68180310110960b001e150900140064a21642ea54070708040707021444110280c0680090701e58018080e4000f0f4038020442407006201148852038003040d01c00b40c4120b5085891120b6003900c0b040c0300d0410700d03a01130010300c02c446000300c1c09442c4c8900030103c0c1d24450f03007655a070343d00c1d1a814010404000b8820000d5400030340901c4a4160302c00200c40468a6002c1c4454990300c03400d0020b400c5c102c440d540080c1d660b41c0d95005608000300400039140503002601d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 551003030 1250 551001780 551001797
    0xa0308010e18070608040204090204090305090f0613030f0f3003020306130b04110a170a06061b080d020403060c08060f31050f10120b040b0c21010501 66
    0x2000c0190b00c400e00180d071580d801c8044244040352042184c5940540014804691030303050760089030448104400a800058001800da80a403d0844980500090a880840c0b4209040c103822280000c10700000b4007042c07000d0582410300150256405034107030461291b04840803001c1c540d05141c4112469860070044404114454600030310980c1e100c1c04020341240040b44a220034080149503040803c0d501542e03827000c06030071100c410040c040c814900d40341e160201c2000180c1c40d4042000600044080d170804509002c402d601c8842c461500303125624a02c4440500d26160110307000384410176841c41d00c003003400401d10400385c101400e0440b103521194071030780714041400a24004c038070071180c0100112252255003001000c043c1070005403480d4a0700040c08001865040d644142e4801035680d40c00c60902c802c10814400a400514800c0798225034100680c0d20498507010051001d030421268100155010003610211000d58404000340da00080640a088408140a0252500003420b0701e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 551004280 1250 551003030 551003041
    0x609071805010f1803060506040b06070c05060f2206120c02061627030b07050c0a08090d05030319060603020406021e011509050f1513090507080a0308010e 68
    0x41020360031031465004800800d5007000015503000d000e0103c030030b0422116090024a44003501e0005014600c52040481c503400c040b002c00042c2c42021085502c116810012807000840705100c110489800340c91007a00d0b10035400caa03160500520b64100000c10135082049805404048820281d9006407a540301309484a00c07103d080b150400300000169110320701040411658050700256480d1a141c04d010750010b1165007034081161080007003010071158400d000300484c081c9884c1d8400b50900d845030070541d48262140d40c0c3e030070201024003c00c0d0700080d101c003651284c0101d407640c0c54101d030880341e8a0500d2401ca640c2c4140241c02c03065400d01d0500007050303a611a0003250101c03581c1d0390017070000f80103800c0080c1c40e8048880427002159070b120300d01c90b603426654004a005250500c0002541c0c40d09016000e02d40000520301210250a111a44807956640f007802080202081300010408501e242241c909545500225594403c1e03024400c109035001c0a86810781d00720074805c011a40b100c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 551005530 1250 551004280 551004287
    0x80c03150a090317040f031418130f061e0602031617040302090103230d090513181209060207030b0c03100b0c010903180303052512030b0f010c11040906090812060907 73
    0x1080001642e101402700501ca4a151032003100205000f0400001014254000c5240407a1440c3d40501e4000d410300760001401c031412070605000b030a082c000381d45008000004074640d00b05d2003038002c048220350045071a6400518044c2d8016540c081c000c40c0003940c43c0d041c440c580a005035202c01c0140d01c0700e0760044e50140f02207030704100030001c2c1d101c0c0d5900904103001c0007004012604402c00c0296140c100002886d0310b0314140d00094003030b10246981041a620043c00d040150300001306640c40a5010400101c041003090317803042101100319100d4031040312004400c042c41c2d01850b02c3e45000f0904242000303040d4440da003268403988581c0da00d2800700321a0b502c18007007480050041082440001d04101c82c0000b0188100141a44507407101c400b966401c24026003206282c0c0080d41c1c9010048141c00d05041084885000742130800302202c0580d15417601c4580b5585181c0159242c048043c2040041d801c61141c09a000c440e054982c000e0a0b854219020300300d0b0380e68415a4880c0106804a01 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 551006780 1250 551005530 551005537
    0x2071214010c051c0c051b010902030615030d0801080a03031e09140c040509122a01061a070222060f2c0907140105040504090b01080c03150a090317040f0314 69
    0xc141c588030300301010030b05180b022001ca0711f0019250b5407984ca21100599040c04401c3c401d17038801d80f88140c0312007503901b407628007001d00c0c0d0100c06205070707903005001c85071000445006095240c07801055803185641c0103851904c212001103000c47c14003241e2000c000c00c002601034540d1040c01180c55120a401c01c200581d032040d05d40d142d85800c05e005202d01000310070014032048514000c06100c2044151503851178403078811405e482c0f65500c290904c901c42d1400c10700300d60303111507802d81e90030f00585d900041c00d0410b49171055500c00c80d600c0e00b44051902190000d030b004244030490f400d10359030348035804c0c4c51003011042e004145a840e40d841a5682040101c7c1c140034100d07107001008598103018400c9942c44c00d50340028113002003484001220390301d6000e483c1106209015425140d490901c1043c9000b46502421b4860b40118681030701d80c900450146901015403c0080b455100c1420f054543c0600304004400b041c13503001c100000c1c8601411020050b601c656100303269801800080c1c01c0902 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 551008030 1250 551006780 551006801
    0x30530121f0b092110020a0210050c0a080a0b060a110d080f0112020d1202010e0c01082806091407021515060307030b0316030c1502071214010c051c 65
    0x8003400f200c142400c110384000c403c0c048a8001c010b0440c030f41c0220501d0200000004042181c0000d0100000d0f40d05004002e00407401c200184468100068184000c2c0160139001c402c1065a000048010b009a00f14070200e16014080d40d41d1000f0442c0010540306100309030785017a1081c80814002d5a2007184000c4c03040b904469042d50603402d2003002a421110081c059030320100d2103620a012580c0f00ca0f800000c0c00341c03600002100b0303d882411a003461010500e150510003007100304000c01020820401c0e001c0040d02252040c0c03419144600018040b40c0c2044171602d00e07100b0504810209101210300850349a0210307081c125001c43c00c600050380841d00c0f0101080305003842401070a0040c059174011041e410045510358200000c6894122034005045062282030340800c203210403091500301814401c5002d002c0c280005001030340e10419071244003001c1c504405c3c1081486454046445400f603002d00030300440d034081c000140300743c00030b20321121a051000003420110701c4030301c038411908 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 551009280 1250 551008030 551008049
    0x1508031b0f12070f0b010b03150a030b0c0a0201231b250503070f081c050420190803090108090a0b0403080c070804030503071209030530121f 62
    0x4140840c00d0056030044003044031088a604003020014400d4a45c817030203041807405254072480c141036040c840101541510707001c0d03a121141400400c0c060300c1c080394450000c90380140d0341d00500c0c1c0228010040070214000502c1d00550303800810110045560141d0416440c4094400da0700314030364040c1c1324500750071403407225071003e0040c0340315021a4594114000e5007560306000306525094480f55100c03004845034003000550020340441100520740400b15410200304a29256441c030007011400b125440c0c5103012200300009a565007060020889204150010020b80d6202a02d40d260071a240a9021410b44400110340c820000341c004a12500a50001501e0320782d0f4505035141c01c4050903500303c00408118178000300350401c000780011481200110381e0b402c01c81c00c00a83c8040d0240d80c80003042080c5c0b0080011803000107041440d0503410900a421641071030240d510002e50054500103c0300100300040704085040e2a180f1808007074185103003914043c912807031840d403540a19000c5 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 551010530 1250 551009280 551009293
    0xf0904060e13023d090803090f0d02060405130b0f010c0f030e040e03210a0501081507020c090405010c090816062304030b040c1413020d1508031b0f 65
    0x240c41d010300c94500c200308a6050104c0310a2603502c6000c0c1c0918944141902d03140c0040144296503c406010010413410303020b5400d000200c2c00096039462403516141c80392425401460541da83c1c00c04507401420001c101007002c40c00000701d14090302c000c402c06480351201d200412441d501420f510345415a000005d0100c4080300c3d80c06880840a6948441d013081d42c51090801000c0100001d20402c40b1840700c4548100c1071035040d0035418001004101441d085c00010859081c0001c0d851300c800d501100ca85200380e40741c8a080b0315100184d0403a55202482d01c051205110066000c50304281d03242da504211243c44091aa669100f0718609610103a543c2004020003481001c6456000d881240d405e09640070980242805400603007054a407505e00e0014403003040b000c50a42c1000301000c0c80c107034590042042c0002c44200701c6104100d8031580014509681c0300250380704208941c070707442c0c1d4100b00c01d881d000115500c2c1c100e5143c02e016280042d000c402d171680e002441f81400003103500200394 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 551011780 1250 551010530 551010533
    0x30f1021020405100506210a09030e0d0515010b1908060a1e0801050702010b01021006051c080903010e011a0607020306011e080327010809121804020f0904060e13 71
    0x103103001450002030740340d01d45012809a40344801082c404004014030214054407404210101f54007800259105103070426583c0000d400001880c1ca80c141100c0c0305140344e1441c2052801c00142c4180340310001440000440c40c040320740041c14010070080e1142030f81680104e001d41c4e0041003600d40e0340d4405004a0200405c5100703200b031164844404660340c2c0e42a43d0b8020103400e645056030218050b03511492000c04550f0304211074185c02090684c00e20085151502103005d40b08182e01405442c8000c1ca807080c18001001d0441b0408800500200f20380c4450301c65050003412000500032a002e44100003050501d81101965200d60700100a004a81d1034601d03000c00d807040c0d102d6501c3d0031015090000820180a10141c00300c1500c841440e02203240c02d0207004594101c0a5480c1d051110742003d11082c144005481c945207000703401d1300d668805282c040b080030300307529035251984203000003407481c00a1a1100502417803072050b60103100315529144030355150101164030302c1805d12003420540 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 551013030 1250 551011780 551011789
    0x30b010824060109051201020703030e1c030b0402090316030215070b01140418050c130501030803060108040809030f030d1a010c15090209010b030f10120206090411030f102102 77
    0xb90004014100070201c580da80021442d5501c00e11030604a503540440d800041c150907010341c0c1085680c002c094111207940220801d0454030055010007050385c5d41c00046640d40b02eaa04449c45075100504807510b001c0545002200c2403a00d000407405214005079a01a42c404101175801d4964010128031450382007020303044900d11070038582c50740700351a4490388464806107121b5250950140e00a0000c62042c0b40500071000c1070142d441180c5403404004001040b4180c00f503980100003440c150046e0b40b0346081c60300d010300680c2c11b181c1d45801a1031400f82c0030301c8000001c0180035031421003845500300a81400525000215200b404110090190000a5480340c4216820204c02030300050080c541c0d008589560401d81002c1c0d40341038000240042018024549035120002641880b91141001e0300e060329980003050090151b100864440c00c01e50b0390390040030502c0c42d13050301251a860040c0003054044000d403101071800d0309100c03010804000f80d04004010040303c0c14559054140c640c02d00 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 551014280 1250 551013030 551013103
    0x10060b03090c130f0e0607080f0403090504090302070806100602010501170604032d03020301030614040c05120f01020a030c09060f0f08060f1011150907060804140a0c030b0108 77
    0xf014261350b9058089100c800d580f041c4d07a60b10400d14014007103854a158043c00221010340402c0310b0300c1c0c4540030000040e0380a4039100c20b80700151800b240a850a1800381d1a2055a404c4082e844c00780070100100980368418043c00c40300039600a00141c0d9072407242e01100c9041804100c030540003c000200820b00514a8004491407050300300b02240030555112a24140d9582450011380c000004100740a000c1c01003405100d031a202690644c24559580ca40c0842e6a200d11170040740070a101d00300002d42407000644610210009540d0b580318086c000b80200074086040340864405030380841d016105400500d070101107038903030070401c0c0350041c001e642c1c41e80001d0849a02c0090810007200c662191440c3e4a86450241c651a10715806003581c0d9081a900c60b400030b18080d9024100708000360006a2031b0200c89c601d042c503d160761950305100100c1003003d0603c4515100c0c203401c00003000361500303a007012a401245500050f90b21041000e4a881c99078104100000300012214405907518030f4130f = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 551015530 1250 551014280 551014309
    0x111803012904380a0308040605191b060b0310090b010302181005040911040e060a0630020109050d0503031014012c0411071704060203220e0910060b03090c 68
    0x400d900d1694030340d40c04090791f0107a00600300060010a0310440c4820040203502d1284450425841e00344420001810321041c0c2d40c2c01078156a22501d00d44c81e551400d20940003081e001c1d250038007465a8609207010010003c1c8030490007074520700e422803100340101d24840d0141a07648d00351800c4520b0041000b02901140100303035030308a0400d0120b10185e0b10351240b204040c156001070a40c51414001c81c50442d942036200b47c0c0d0918000c003a400e146c000e0000e10700086410300030a020f44c0000350004840428407500100e4200030016610014400f0000c081d41c441ca428403290021b854440300307410201603030540558040798119452588405000300609101310f1042c070204802e1920000280c140ca029034081c600f18403000032040180703c4240f60b100c051401e0181014945031030690001d41d20b01c1221038001941d0410003010140704d409080d5480203200056000d46c2506104500c15280d248500c010341d081c51401400141116900d41aa4441c0c0d0500c400b0303110412a0406105580b00b1070482c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 551016780 1250 551015530 551015539
    0x1b0609020102032701020d0905010c02090a1512120504050108130303140709030311070b0406081503030414040b220207030905030d0c02120111180301290438 69
    0x106200c0d011001029003044004400840c402c0780c2c01800a401c140010b00c02008021562005010304d0f600180a030380820b45c140c3c1e1100c419560120ec00008000408641c0e8801922600004020b0040f0303c400a40d1801100380000b903011444d000e907a140328a2280d640400d008600003203810803681840070081e4000d0602103010b01d05015030310522042113501c1c10215156000078014161b001280d803074072140005c024101070b810f020342140280114801d48040003c05400500c07404030800090301c01c0c01c000350459032515103e40440890000300864240107034503008000119151500200810340d00e552400002c904100c3e85000c0070754005001a0140413103500000f0341ca032001c0000c441e5081d400d90f02d44421b40e00d10310402814034002200d4060aa05188405906240c044102c81c07076041080c1e0810705481000340400c0c00750030700500c40045614110610002e0555540b074040001000312030401c0f1b0380006140c450050308030380c01120050421035503e604200d0502080c000014001031 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 551018030 1250 551016780 551016787
    0x90509100525030908030a0509070807080c09060d0b0103080d2c060c0c07180b03030304061e060e060405040606050307080312150303310801090b01061b060902010203 73
    0x29905015500195121400c8440b920184000310444820042e108011483c050040380c4c0320761280f02140c00050070461106560328007054403003404000910041c640c0c0d40594542a41c0d44d1079417078031401804601d030b004800013000600e55181148082d10910b51028880c0c4031642103458924040e04201400041507603130b0340324070301009401c2440300301c106801162183c0c01d40340081c002d8140031024001c112040400c2c004180858000f084250954424130300c40440342d02c1042450014040141103070303406010000a210520149402130f50710046800260030340c69104810613401c640d0075103e407281416400380483e0030b5241030b4100b9500701d80101000301d0125103c0001a080c01c2440d4450b80d0141c2c40000c0002c28041c0720401568000e81c0422031903c038903680d4001c071751244244641400002c0880c96141587d0b1022500c1502c00d0b07002d958080c514940b0b4124050091003881016070f84809802d0000038207030301ca041070b446240d01002c0086400a4156540400b401804e0303000c0341540420f0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 551019280 1250 551018030 551018053
    0x2007110a0f03060501080c03160b030601020312092a03191a0c13090c0c02042a030b01030f180206070f0b070512060a0f1404020403050304030507180203040c090509 72
    0x7050180185009000c00602945441017552a2014004003c4d0107600300d151824000c0d03080b00d403098100c514008601e40c5d03985e5403100407170451240f8020342e04074a03103c0c82401894000094000e10701c1d15000103001c05520390305c405541e240301c0859420b50550040f6200d5250303020070311480c0880b62154081c001c2c04404044c00d06a80982214040344911010952112014095200c4002082d1510003003141d4a841640141030382500c00e030190203591030741110f190b88800c5032603442c0351a06d80f0364000c15030f4150701c000074040c2c403d5000c0d035400281440b440851010b000c1c400c03004c0031103000031412803509059080c0225078000900c195200703529010300501084401041510800c06a0359495072803841c0b149054507080302811560045446400034802e402041740d081094484a14a007107010381c003c0d00040c00b910461300010b001d4000071500100301300c40010185d0035209000c08030203c08442c2c80200040b404101d40c040e00c0030307013540000c0241f86c810f03030711040c0c00c03282c01400c0d00d100c07030481e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 551020530 1250 551019280 551019299
    0x121009050703050f01090b01091a0d020102030c0a030519030b0607121403010909060c170c090f060c0109110904030c031d0414010602060108010207052517102007110a 73
    0x2040f0008143c1d440395441020404001c4501c1d014049a00381041900c015404001c0d513002501c594ae8040e8141c2e0b00300300c0a5a000304203a44080324018200e50450269203001481c54119174000e4224081c8005249030050203400740c804001005010607003496a00e84551004411040707001040c400902d940045d2000003000441c060040d2203404129806107103814002c980000380c0a104018048200406042c841340010340c00c01c1c0070500f0540c480010000045191112f03c40240e440680040d40300c140c4c038010340200e1100d5008000e51140052100240b019410301100e000b0002001c0c5a0480006030013922490413184141020b0415201c03090041400ca804581c0813a202c02c43c04001000380d15030401ca401c3c05020180000d5080c8003080c0c0c0d070255100722507003402c0c0840d5500e2460b60a5441c4011520000300140130b403c1c0602071584d02d41a0b01c034a140080518405d080036420906d80c140300309207070404034103108040d1502d502921200f6840d043d010240e0b500407a410800555000d0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 551021780 1250 551020530 551020543
    0x15060a150302040315050402091f0506041205060906071b031b150c02010c0c08070501090204020f0a14040b0301090b03071a0d06050405060d030f020a0209040c0e0612100905070305 79
    0x40c01e44006a0329419800d1103003008080c0c9a0280350079080408000050702c801d04101e40105010440703070243c2c50300030091a10f0312042d03001250811008100010120300d504051011140907000341c4000e078407140f11207510341e10110351210100fa04035400b41d4400820000403440c280c001e14205401c50200c0c61036442c801c0c0147c905882274100c50b0b03e10340e5521451300c00c80d11205402e00003003000454980e4050300074001c1c040003818554010901c2c0d001d0000c2908903610441d0f0061045507564400d00040419800c520300c3c010020350140070703407021400950b0440d015a150030124038107582c42c090309813001d0001500e459030180104080054070510380c00b4002c0345d88050000b882d48450069400320102c030305a620151040e0308060600c41c181d280c5601d0050030070742502d4601d82400704200c09034034000e00c07072000a401400c00360030001444001c1c244007042d00c10702003151a50f6143c000c02c02071000c4c00c4c22142c1c0042d800c00124080d0545203680202c044610450985030656a2510781508040 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 551023030 1250 551021780 551021819
    0x41d040809030d08010e0f01210c0504060b0c0d110303192301080d081006270e040b07050a0e0f010c050304080c030105130314090a030819030c0302090315060a 70
    0xb41c1d4040140921b80505085940c4030807401c0401842d5031500f0322070103e04c0344141c69443c5021900200d207052080802c002d44c05014040c0007030001c146d898201c9219503003c0e0403038040c40c8c0611480300302c2051240350b0703d003445c1c00214004c505507102c580452801004400c00000b42c142d8500391410318002c246c00d00c0d0494070705150356011a40c5040076541c20840003448400070040786d0f000308a032892031082e150003900d03e40d1030206940f6110038507003102403102c402084a259540100010039400c0900b80a126174441c0d01d8025854964400582e10b600482c100d41e40826040044079916040141d000006814145001e880f071124580781c003400d40e80660002c0c04150091403210441e42024003e00d9003201060f40c0c90f0b02c80d928a914000c200380f88290703103001d11100000f42d580550307985506050103590400103180d80c5a41c0b0040d6040404103276070344100400e040c50000200c0c01e00a209640030300d2000390282c6600d100d400d440d41c42c500130050a80c2d81c84081d08a01040c99000c0000e500d2001e07 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 551024280 1250 551023030 551023037
    0x90203100b010810050d0803040501020f0d09050d08190c02100f0b030c03070501141c061205010c08160804050f0a0f050f011a01050310030203010c030b0103050c041d040809030d 78
    0x2010100005000f84030051002207010410001040079031100140c1800c00754125107032607100c0d00c41c0c1c03034054003910a030000c850300d002000c94003010100c1c05078001071049208030101c0b04103d04802d8142c80100003107410201400003294a12461021a04000408012807050340c0f41c81140c007184208440000e002942e2040e99103510072207034241000030260f040b604600519616207090002071100710f103414008649180440c81e02d0340780d8201c0c00070703503d07480c84c1300424881d0f03d0300c41400800d907082d0a1004e685643c01c0490111601d4000d0310814011102c500c00182c1c0b4001410302500c4980e8040c104542d544a44510401e140344103110109200c2e20840360ba03201c0c2c2c07285060080c40d25080c0c0404520b142d25100c0078203914170034038071585001d020a0901d56125640e00038202d1074400303142c1c00030b90154284200b00f05582d034103038040c58011100b600c040100e51603103100007846001e02d0103174035001d034221b00388240e0002032482e905a101e842039032114a86948200440e08102d101c14110022 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 551025530 1250 551024280 551024291
    0x3100c0314060306040b060d03031b08090d0f02030d0c090b1201050307080c030c0405072d03060803040f03112b1202031204170c0303090a020117090a110409020310 72
    0xe4032000d182c020008600901d001e003401e49441c00b038003002034802885143c2005090040600075040000303c1e19508104000340d0071844e0001c5c00c803100480d400001030040f00c5104804c203000e6900820070707410542c01541080c02c40405040101070400c0d06100344080c220300014451000c000500b40c100310800c07a0311440d40340805040c9444203603040700030503030017400c1520015100001c00c0e0210500407100883c1c152110a03003907480c81941c40f8000580203402c0300c1030704a81d25148000c0b09402040e94100002c55441800948a000da801807120717070b09502000b0404550800b80040d10010001c003045546170403030103032541004500545120b0b0640b04060079007407144a814284200c0540e0014524200b0702c6400b41c00003000041c401442881544580c0740101c0c092000d60b4010140f80088941c1c1c1e0609940081d5124039504040740051b030410445082d03014a00788035402050b901009002c508a650b0f1030501201200c840345400640e00c032013803c0542c0e01001020704146420100040 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 551026780 1250 551025530 551025551
    0x61e050a0b0a0e040903090e04060504020312040303020a140102040f03030c0209070e061c150f1e0303090e040203010b092a0a050a0c0c15020d11010b0d030c0203100c03 74
    0x1025046a801001d9081c01408009405a00b003108030510143c21680054140d4440c40d042e9442c48980e0030030030f5040658010031080081c680d04c41c2c6d008074000c030111103d84804001c1b03207145200310b01004005801400d00030300051045040000001400c100243c10680c5440031007d86408603807003900041d500b41d91200640c246058840c3d04200c0c58509407044d0114400030030300358410300749048500d1600c01c40c0140000016030100c01c1d0a0f2000b14074001c02139655101c2c1081d411240180c2400e03525030130207620030f48606040c0004032685921594400c41c54408182c0701031034000d2040c1e8040d52112490071a1b030351fa80d0500c91040a5800014003c6c074002c209428200c02050b21000310003070100302c08101c16805c181550300302c81d81d03442c102600069034540440702c601d0710f031301c00540203a02e890b06942080c0c02103400d18200c52140e0f0b440c44584445a102030a0f210a90062504011507810250100340300342402c1d8081400030341280c80d040000c02058003180c60810410001039604d415a19 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 551028030 1250 551026780 551026789
    0x6070e2b15060e01030c0513140907080709140f0924070e01020d05041404060902120105120601141017090f0c010c02030606010806030a05070e0f0f13021003061e05 72
    0x402500307030b4100da00341a6045035100610b0406d6805454410208a058052044003540110600d464070a00d0401541014081d0f55660071290040103094002c1e802c01140c00049071140500311700984d880711401e5240c030005506d030040d0203070a01c88140a2000c4c0b1010386403c0d0303d101512112030034800314451401c000010020441e0704189070454001d003d130001d003182e00500b40d40903101129541e082c2e0750381c110005801821580c0c000d000441c00400c000a280c100425424100d034010781d0104481981030700010b841d000b09018810b0210b4000c200e1b0803290030851800c40070303018141480403500e0380240350b0850604007211409602e0340402020b80c03e071346082c40b401303a1a200a003081c103840704082e4001b0780c07903890041000d4104180351001403040e65080185040c02e58112065170203a54940501e003185090407a5000000e080a4011480c520380103941d452080341a41400c0141420940c200010403488800440425407206004550314007070b421141401c1408117810840c461402d020720 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 551029280 1250 551028030 551028041
    0x705030a0f0e0a0e090a021c1101050f030a0504240c0207050103151e0b0301121109060607030305040204020423100305101203020307080a050304060e06070e2b15 71
    0x1a800c1081c00200c0380b0356501c490800d6015140741241c4400d095540c1c80d83c1e50b15100400e14040d40c091107280071510b060010407485070180380201c1c40034001c00c00e0b150041d150f600c540b007000071003030b08100005680c0c403400340d10058005103d41150074480d80c0813a510104a23400b40091004595104851000d1540412090006001c00e090620200e5a1700c51201342e540784c0c51180c10070503803c098100b080180c50083c041701070302040c2200364482d41c484c1000344282c10111000ca80c0d440790581040c5a5280030382d0310740d115500003804949464401e603800c42c00b600b4041c1c8100e0300280c090001060841c16109140c00c4000c0040a0300824417016040001069444030000700b4140380c10107215107021040e82840c04d640c40708400b174100c0302e0765241c105d01d184030386000030740790300404142503040b6544000114000c3e0702604050180d00041c110f0551201410307510000440c10694445030281020600c68000b198101802900d0100e4881d03a4028400628811590f03414a1170500c400c441b614801c4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 551030530 1250 551029280 551029307
    0x18050a050109060c26031915090b0604080a030207060905060f09040c110f2107171303080307081f0f33020102031909150e0115060306050301230105040506060f0705030a 74
    0x14000d446845042301c80010f014000c5e4110a5106c000342049622000119801801254102c800075041414000d4880e821800307a9400281c01300d0b40002d5514004041d83c400000c0d5031443c0e80740c146903034100030040407034400400c1840780780710b01c0744240f0b2800e00c05042804200320150204a1502c11448580e0080608060400b2424095200403aa482d540b0583c462003c1002070b0361200410000307117403402658001040a01c0c000b0412100720342c031400040c040d280b2110a80071602e060994510322001030f010f44800b581c1001020010182710300401c07403030705002d021800b98000380301020181c0c0d001003030042801b40c0c0d000818400e50980510300d40f080e030320b0301384020440350241c0d81e201d51912a422208203c00d0340c940b442c0d004100383c2988948090482c803940b0004c0241c3d01e00001e00502618030416105e540f80c2201a610207120a010f034180d040d001c1041c802c0381e03080000304402008050b0030250170041c180711203001ca2040c403006180b441c8c0910011602ca030110740c0010004c1c0f142448 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 551031780 1250 551030530 551030581
    0x61c09050106080d0f17280e0106030b0108030315010e0d0b090304050a0b2d09123004030210021c17010b0f070308090f07030318050a050109060c2603 66
    0x1a140c3c1ca2203269011500910b507620904040c245a203500180400e0411f41740c60518504041100c1043d015407214044034400c07401220240c0e41c07000034a0716404212840500300b200b1b82c1006c02250310915410074000001800886040040d4560900907403085541d03c6580d80001004d00079450000c40c420b0081007203858581c50030303c0805088101c54012030320910440c00c14201038a00d0403e40341a501414000b030042d84031a0a0a04280d80d210110316120310401c0050300b44060000e040c0130341d50130031310760b0079000c7e440d0500e507909106812505107040d83c110b0107100b4070008000d0641c070400445c044c490740e4100300c80c000540c11480d00001a4001000b800040001d0f070b0240da020001d40d400283c044c10721003400d0b511000494185480c0410800941c004e0300700c040105500000c5070071203601c1c5c0d509485070745525042840444407070740c082c00c1d001c940760110812106209602c1100143d102c3da08101c50f100103101d801140c0c40080b0800052403001104000401603040780a4500e50380c401c8 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 551033030 1250 551031780 551031797
    0x20c1204082806050a0b19120b0604090602040e10050103020702010804112209030e030c0f091902030c0912060124020102041d06090f0402061c09050106080d0f 70
    0x6a105a032552000712964020b55000c408481038480300b684104500d03000711090105291003000240142aa600c090344907920024030141a0400110407509035101c00e0680304041384a42c0302d0f50b050900082015038061307201c2e5038520004001d40050001042d804640c1041341c2800030124216040036006a4101881440550003503039200c005560059000040003141c031a00402160b1400c0b07040c840024a207a00c6004600303120003c1c3c0c059000345000e42d0362803100c2d81040080684907118022115072050b031140d04100a458100e22064021a501c3c003680540e0300c15114010607a0412a18134078950300200d031290300350410703110030300011403400007a0040b507050183c0a04800d40340800e500c400740070707036004409060003541120045c00600501c2c5524082d00d803803c5507404000c0f04c0300350144d80610b010610440416815500940d801031030f50f401e1140100e5944040c541111081040340e4440100c440840c80c207100b40030280001c0ba01500c0da0690055000c2e00412804446408010081 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 551034280 1250 551033030 551033039
    0x1032c0715111216052508070e0a05101d01090608030a080c0c0304030f06090203120c062d040609050c0303090d060b0604031b05010915020a0f0203030418020c1204 72
    0x201c3e103583c9002079003850588405020300d5502c00c610071450014203611541501201c1c04004e003140603030340400d08000a2540d81c031010540d803070340c10078801c01115a0b200404034a4003901904501e5101c8011000d201c440c580e030300c001c2140070b10190a41c40b4031074028001030180b008030340100e0001d014600e009501e80b1006d2000204040c01c010035010001801003404002d051080c4201d400035500007104950306086410400002c0c40540000c82c4280f03d06e0402400c503203002010382e041041d142c0003421180d03440403a140c0c1c90021003030941c1c103580c405103429200c0c0d0f02041c4009000e54028100080c00d0702580c40c115190441c0380400c3d9100b64018014600d041d42c88021030100954441004911414500b01080716801607030030041c400524550b00f018000c02d03561159080b140240c0e14566925035500029482480d19850140181c00000d4141c4c0820b520341ca00c401c500c0c0c0b026040381d25003a03441c0b4502c0c00000302c1543d08450103400240c04510301c0c3c0c00f04080c244d041c1c5c46413049454185031 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 551035530 1250 551034280 551034283
    0x1006020a031107090c051b010e03040608090a0605090d02010b090108190510020f0703021b0603040803130503030709050109142d03100606020d0306050f01032c071511 73
    0x915002010864001102411084248983c1000304a00c034400d204810705604050306580202500300c000604005690030a20014041c4103c3c107401d50000e9440c090600380c0440741c60380700804811482c422a2034280c002621889068883c0301c0e540c000d092010390382c0000a080d80d061b0a00c242c810505039006000000703010609421003540d41108500107050f51078a5400e004000c8000800701e0320101d2590f2441e68880300820340e080c441c2c0c2c00d0380d0b4090565044c8028002c101400c098210702d0034000640042c08600081d174000c003030044515841c0720f40e59038081c5590f03c01c403488400502080c0f0104706958000001c00042e0004001380700c0a0540c09001c24011200c1a102c0582201d94003501904da4410200c845617408014064034829940d402c1014050200c1c0e105590051103081100103185201e449400191a0700619200348540c00341c1c01100605030280a02e200f9100180a41c0b80340503821488603400d0228401508100d440c00701c0550100c80b03501080810b01c10481d6002908520 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 551036780 1250 551035530 551035543
    0x612060c090d060f060803040315050c070807020d020306011e0b0403110f010c08030a09140c0a0504110f0403050a02040e0a08190e1908010f1103040204020a03090f080a08100602 78
    0x6007660650302c10541410124058040b038a050080e051400c800031a8244000c8028000c0c2c83c06111b49814070310f42c10a800d01103804c101c0e0001c40e411814814034000500701c0c1d0003030144500003800c131044805a600002d041100c21b0340110212400880c02203c91002d03000e111006000c0145000d0800b441d5880d244000729034641194855141040f00c1251a802800c04c0c08415401c69141e540301d2a220b54050014140c1000c2038a000c8012115080042c200087ca0940e4101c00b814103507503146000b09001c06410680031840c1c4c030000510a084000c07865502903c000c50041005115003c0c3c18010700c41128202564581d65801812072440400c14440c01c580030440c051461f00f1109208540442e500321440380c12503400107030b00d240140752840d590710141c242d441400007040380000717085104c0110ba00d44802a1030842041c80002c0c007520303155000d0040740d071b814140414954060359400d4000640c52400326070010b030115020b038400e580500f80641c850b4280649800607814010060b43d20711 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 551038030 1250 551036780 551036797
    0x2030c100504240b0405060901051305150301180b090c09130c150210060803031e19060608010303030513020f120109080414190609060810030c030b0612060c 69
    0x40e00c0310049030402805859544080d070619981c0f280c401c5803500e0f40d2024062080056108034105400700304a8034100107202c2c100c0d0401008507004402801c210005413000030041003400c2c480300300080035501c0a00038900030310401c882c1c09150200030b00d00800201d070b028001c1340481d03115510300340c0151030341429203401c172182c40c0880324440b0031403504000c14162604010044c4c140c07800c011014540004a98006101160051000541b5200c10719540d010807901140404801c944081400003001e02207500a01200300c84000790a0340c00c031080079100c00d54011070004864600400a065142c412507422a11520b061822001240c0000e0884501c40c01c41c903115400d4030040203140d0f4825808145655031004826840c2e942c0d41d624003105444245000340200c08900900c181c01c80800380607810b8503035684891098500b00301c004c903a03a4030014103103800c0ca2001d140c0800418851010346004511030b5004a041c1e03d0810284041c8820301d041081e07081d0f220034140202020707c0701c141d80340103 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 551039280 1250 551038030 551038063
    0x6210e120f0906040e0406050f06101116060c1a04030c0201110102120a060512031c0903110142030303150f260a031704060e0d091502030c 61
    0x249003103456006a0711442801603801500014000b030402c243e010103d2240d40210f108011503542d142000d0118101252b2a84e880304161f41c2c840042406a100074020072106401c0b903001124165100c0c40605294009401065400c28000c080009401e00321204200b0f5000c120900d04240c0c0d0050300d16694400c00034144048100003c01003042541604c04601d80c20325171a94901305464884010800390207100e0003503403400800680414000203e4042c00100032202180ca400b0003125030041000402c1202040010780e000380040c0300034051000b000c480c00c804079411480081e0403000003600d1030061207210240d41c0c8400d06402c03a80c00703102c080780d80604000c648650300340c2c914140c001c0241c010754031040701c440300801d2000b510348a480004a28046018000503508031491ba40c3d00c074070381c001b00040d00e580848244240c600f410203800034070840300401d00c140c090807a1400c12600050000c00941644c030100300341138900a0241101b0001c2c00036500e002c85e0f842c01962512894418480306 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 551040530 1250 551039280 551039287
    0x20d111207081f021207030b01120c1e05190206101d0f2a030604181e110418020108010614090d0206040504060305031b011a12070e0106210e12 63
    0x250103c0d80441d44028202003104a191400c3c40c000b60041080c0718250b800586404011900d20041e8401e00d103190300d840d1504407098030100c3d02c03050b14105800201080010600c05072030004e000003800d000709405038000d06820304c0c181404081c201070070f0740561107040f8008800899081048605d90300403440390811072281c0e42e441e400d10701c041603041d080d0004603070b020245512440c580010354000c0208031401d02c038504860030a1703519010903aa01600c50001d801d024008148209801c0c6915842413074451000346c20000001c0841e403550382203040d40d204034111241150fa100003003a01400c7e1608040001172042d025410f03a0b0f0041841c070303030302544004060b00155510101500e00619000700140000b40d100e1600c59240e400030207112070050100c4040381003001d0f042c0540da4000c00281d030300d69091840c2804000d60241454100305060085000c0421140354034000d00d4003030101c2d926042201c0d001e0880300460f0078180702511503030740d14048038254a10400300b007084080010703500c41e584 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 551041780 1250 551040530 551040583
    0xc030b06041b20031b071202010f050d0609051305060612071406070c030c08060a0209011b1b0306050105030f150609060a0807060c0201110102120a18020d11120708 72
    0x403c0401c554a98055200c0480d80f1600c0c00d58088a0510705048036060303c4145656180f2511450302528009010580c0340d540c80341c4d0f1501c50300c040d04082c00028008a01b0540e14011101101c80603140e612440500a822906201d0301300903458010b4415262504407000f01181d090b03c500207401014105654212400c0059030b032401503903003140d008000716904c103940c0d20300b80b550b503049031061741424000c0c0000107020084a100b0741c0e810307400684a440002401d0860301d0850010241d048400108503040c038024101006075072005148030741d40005095044c07404041c0780c510001e01910081d44040080c80a803880190203075085070741503d1340e01d0176071622030008400e582190070581642c0300300000002c585520490650100d4004c0e01c0d0040380d843c040031018243d00c81c3d994074070840f001d000c0c04100b0100352580000e460512551070307400c445045034005501c07420070000c142e80300345031520310038113601d0141e4180c40c12688541c0200b101c5c43c90103881c0c6032120600b1314014080b0074560006c84 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 551043030 1250 551041780 551041817
    0x1c021605040507090302190609061b0320011404200d0602093d0903081c0216030504030606050910090209030a0f12030c05130b07050115030c030b06041b 67
    0x7000d140c0c010000340c1d0b41840e0b0b98001f11107041904c070b10fa002a41410000614600072201305400c89003010820024540d181c405680c0c0503050150034010120030405c040d4940420321401c5d440c03400d5200c2d4a6420b08250030840100942264030b252495030b084003c0b82190340d8901d42240083d8007020150f01c8802c020700152500c1001c2114240e001001c02803900e01c856011809021407203001c0c2501c4072100e01c00d4040b11200143c3c0002044488200720b612810600941003000c06150007a0141c034201a183c009211080743c0741084001c034001150500801800b0f0180802400c1c0c1030344c0c6141c4a103800a084042c100b0a0310a50b0b072181e03070020300c80f0700036282401595103481d003265052200c1034540ca4401c407908014018507000901d0702025141481c0700b441250140790011400ca6051f5091100106403076101800c1191199030f00e41c0c99890880603c10404000c5001e41040d0035114a50f003071901503503400030b00e010310907031a0500380c4030a107202402c002106002441c091041c44200340404 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 551044280 1250 551043030 551043047
    0x1060803121b0705060109050106050f040e13080d060e0114060405100c0203060f09010b090610050d0609060b040810020c0a03050912100b0a0801060803040b1e0c1c021605040507 78
    0x10800d01000441d030f000d01000142882c103d54648200700001d0781c0c0e80d4012151402407110707052140360100300402411040320340b00390700681680007800c91504155980032035079005c01d080f101c801c0d84881082110124880c1c6171401407a41e1205402d01c1a12000050004d10032401000d1042ca05511030058081c80740c0f44201d58564050700b214044d080c01c0c15420040101121806220760a103110b031503890074100d4941d13020304000303881040d26165181041d2504d811154180c1c034010f0703464030005540c80660085100400d1421041c43d51141000c107450f04080d41521010303461030040203440144a80005d00100050305454450f444030300e503c0001f41040c0004241d00d10fa8481c03409022a10401940f210350192002ca600d03242c02c6544642040c203071480d500c00c1400c1038200780000c00000210714010324110459911480e001c100010840405401c040d600300030701c1e4040e00448820510583d07041c0151100c0e4001031000d14162041641401417034001c242c0030b03685a002080d5152301400700b4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 551045530 1250 551044280 551044321
    0xa031202030c07080a02040b04090b270102031303081b040501080a0f050f060f03070e15010e0a1401020105100b090f0109080a1109010614121e09030703020105090106080312 76
    0x10307110510358904c5a039545614224080e80f10301d150103441c0c48507141610a042c001640584031184646c1c0c0c1d01032110005400a5020414484c2070390b94407841c800a00c0214410b0340528295500c0510504000341859001010412410b9140d4001501c1c000e030b00040c0c8044070824a80503007103940d103004000103041da009940418600f030809101c142e2040524040c071543c803c1e112100044a10b00c1010b90703441141c8140c6801c9400c0c000801d64102201030b44040d0240c06042101402c1d604902207528803540b40d10100d000455100c1555056a0a00a00d030b0461550054025264100503084140784034400c5820b100701c02c5d012140d0344d2a401404248001c000d5641610111185800c0c140401c0c220b1000c1c903071052003030b070300003154072402058250b402c500543c40441c1404140580d03d001d084001c0d0011003108100410101407080744440503100c1c034004000313140c460405140217400e5a03070150010b90164100042400010b13000026140b200410f040f045d0480d80300c1c480b000140001c0c0004 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 551046780 1250 551045530 551045533
    0x50706050103060b0f0105041a070c080303100303081303210e16050406050402131703130b0d0513050c041109030303040309060210151211040911040e06060a031202030c 74
    0x70502070282e120701d00c01c901c05e594480c10303140700400466142c0306034060700d4142106060100c1e4204401d5014194051007440d078107032015100d6100d2443c40c2c02c00c50b604400d40e00300790350500400d903110101d150030040c1c1490310b1401481c2a07902808990907141005425204280b001e14241c080b500001207068400c810b44e0b40c0c2c0355402403040b00e1100c260140c00d00441c10090b001885040c14421149a0040510041b121608101c103810014420f40005400c5100602c500486c503090500f0f44801010741541a03540c41d000002030800b640c600419100c01c10881022210201d180411380d038030824001c0300c001070f0350305144520003040c0c001c07203000540500c0040204410550408841c0341522426001c56180c1c0da080032540301075507111084050703c40c1c4440d008025000741c10000aa609200d20112000362245401140c110340c2c41e4003040c4c03140e070950080000a401c00d44507030f50041d06064007518151070548080b65002d0100d20008007500700c03240c2d078840110b1090054403040c50302c503030 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 551048030 1250 551046780 551046791
    0x90c0302010507111f14030f07081003060c020601090b180f090a0b01030f0203160f03020f2701090c0c080712091d0f070306242a0b0915040b07050706 66
    0x85c2034112007070321048400f012410b0000103070085d00c0da11083d2440341038249450596a600e203201103480d80c0019102895000032081d020000401501542e82e0000a40c0d00400c034561401014005403200c2e016494080c1da449003a103480400001d55240d846a40356456041d02c3e1240e091192a1100510700034108d200d281001104004d402803a911449000710110386e07800f20310301640c00c1301940b18403601c844840410410001800e200c6048100c07082b00414849441c00541d29038102c1c03a412481b07081c41c5000d40001801101c903548030b119000d4036103241c0100100110b50780c00c502807061010141c10320310403815039030889200700450b0019088840e041c104000b42c50500b01182d10b820344d00d40c40a00c205c0000169401e100b80301d410104c84d4038030108c80c6650840d0745600c8045804d1080c0d0420440c0b20781242030740b110150400340c524080101a08540100c50829140015014215020580242c0c69540e40100c450000b2a00b29800078a420340b161507004064440d071140d0f0100411190510 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 551049280 1250 551048030 551048059
    0x20111010606170705270105071e021e03070909080706110703031808071b08060705040806090607091a09091618050907030b010201022106010909090c030201050711 72
    0x80781500c1c1c20f80c180d503e20692610790f0a010390300e078021202c0e1100e11286020041e400c140c0440c540c3c0c02c082c4410f0604628080e015100c00e84061401c141202003c07003c40c151408509010401c031082d40d1a0000e0781100103402d42c0003d44643e528420080117946070000314041c031203001e040f981259840700041001c1030309100700b0000c80e0032440003a0086441d144404050120202c05102c03860380c08615031b031900890b40c1d510054130403944c52101010380300250210380c0240c100441d174001c01d51512215255407601085902d0002c0c01002e04682d40c0082d414040d500d5013101c008015109100480901c20f410028108000c1c0a00d44416030710003109400d110030120204841240346070207070742c0c017002c1244250700d11007504100d00c5000d800441440010340500e101c0c1d44039060100d4140700161034090440704450801240400c3c0120061210062000380e6800002400061843d201e09001d08603a43e2680c5800d04070912010781440070002e920300420245001440164100034400c421003c48c5 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 551050530 1250 551049280 551049287
    0x51305280e0604050c1504030201020303010302040f023c0f040504020a050706320603060403110a05030f1207080c040b1309050a1a0d0c0311150a0206060a140d020904020111010606 79
    0xc0245d240c05820050f80780d101c000d98100c100c6040c0da406800440c9164610740c2408010181680c0d00c465040e400e000c0015088542c07209400b804242d40c4a19440368551420120030740c00307540c046c5641003800c20956090104200a45045410481d4016110001c540c0140d03018428001d0041240d490004c0412008400e5205229080c80c43e0b034100c904444229100740c1c42100591343e03d98945d101c5400a070000740303c0d89101722a1851a0240c907155066030791120f00d0341d000441c810242d0300010440190b49820280d4195010402d4034205000e400e00c403540744180e2103107010b15001c1c0c402c00225900551500008240280740041d401c000c0c1e0301d064107100005044d803e940701e841d4140b4200b600035925000d0310340f9410036000400383d9081032455031854480000030918640049510810b0001d030341c00140500f1a610300740d00544524074100040240000440c0c002d210b40c01c1c40001b01c0c000a4813002d035260100c550603a2503040d50b4440707000503101d072075400c400750300b456007000300103d2178690 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 551051780 1250 551050530 551050543
    0x201030e031204060f0e0c191d061c0c1a3010060e040e0a052406032103090f030a0c05010b0d12080c1201060801051305280e060405 58
    0x107100c04001c00000405c1e2841607032041d901085880c0d01c543d030b004226142440c0d5101071841c0104040300c40d9944e0704000000034044040a0768032036050010490075081c408001c7c1507503540f42150f219400c1c82a5203480080745103000303144083c18241800e0384103010180031200e9020072008103800400b80040ca021100c410054096241707001c2801041034140c1c074001c0a01660f0300d54441c04480d0f0100400d020040882c1b4190384800e100d1002d880012801c1449950009803070903841c0310000b1031102c11000b0a0303001502ca640070368000310260030100682404049071103407100302d10703960b80c80749403c451410003500302144a50200240c41e015690300314038002e0415204400a00c400460401007116045140c9005058030740c0d1610701001c423030b108191256101128401c03290410110300112141c51000b6040440030a0300724005110314981040e500e001c980b002101403040d40340c100c04043d64109900031110000c40110302d4540e00c1a22a04014080000602240c03454a0300d4209281c0e940c1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 551053030 1250 551051780 551051783
    0x1510081204030213110901050a090939050f09030115080106080f0a05070b0c0a08190e0910030b0910050c090a0b120609041113090302190b04020d0201030e031204 71
    0x180146071003a051252030040d1189a65142d4805d0f08104240c00156070395441950302c4810452800c0010800ba1458480e80c101c2c06c0c03108a024010700c083c10801b1080703107000108480f100c081481440740f8550321400301c400801c90710864640b02ca000d100032a01400c0d140000099841542201082400d41540701d11308950300081268001405108001d446015180014015400012003444105412401400c05074107003012280d0400c040e883d105925005840c40b56400d60080d5989045903500041c195071150040364803000320b042a90700402d02c240982f0004058402c0000022603a110500c50402c1e0900d1080c414051860540c0d039858403540b00002007449101e1591022442c000c2000c103403217a409002d8484001c45c1c0740e070010443c20400c02030048940e061104a070340e51517120b401780d4002814080c1d001150030398591501a06048031248020800003042d03800c8404980c510400b41c0d00507030182d278032040c07262150004801501c2c503014505d51906c0001a0b04082c1070000300b1491007903 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 551054280 1250 551053030 551053039
    0x6091b06090e0138120109062103141b120316110a080c060402040506120a020f040e0708150105030d1409190603060315020a0215100812040302 63
    0x9946920065480700e18500807604560800c0e401441440b48070742207401c2c888150861003248a02079166504440c4424003149034034200800c04601c1d000c850710500c1c2c05091030000900c802400c19203600c0741d070340d02c040c0380c0a120380094840005043c003503e25803101041040030179541d0491515080b40600001030213100c4c510501070000c40360038103503003601d0041c2082440200c41d04840740c1c04407901c000ca4100e07800c03203024121010313001540c1c1c40010201d107450300010789224a401d0041104407030b8000c081c0c034000c15507500403003614400490380302d0702c5c984d040b91314448090150020800034100900c0c0d903501449442c4011600080c00902d03070341e1000340c800034034540f80c3c1c0351010700d81c4603402c600005e03010810140380141c90389c07181806095026800741c0980c0840460070b240d1002c24000d58030107808655210400e0040c007440700c04940c100412000154075201d0300141c020354500c9510000c43d4500440d5021038038000031102031070024a0a034048440ca001d0507401101a035006100c102d229 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 551055530 1250 551054280 551054333
    0x30908030c0414270405010b0604180c110709020c03090a0906030b130503030a1107020919060b040308030c0a180b2809050108060301091a150a1802160609 68
    0x43e032070580c10981c00002104510103070518562003844020350080d100b1900355480d501880c00540303446001e4001070000d4856016802501840c000c1240c1c107034041e243c01c010845000c11000240010000100d490013240113036112007400090341035009075089117910200c11040002e512034a50090400c0d2402800807029030344640300440b0102c1e001c0680185160024030005001c3c011b50307840003407005080c40d00146400030036130001e081940c0469180810a041400110782e1220903c5943e01901303268621074174003825901c070802a400000c2607070480807000100c0191807807007200212248601d50542c03847c120344484511205400290040340419103003030460030240441c00c14401c1062030790702d03580c0e80203044c05c00445020000a122542540d01c580349000002c90552501583c0054050444c11700d003010f41e0070510920205036000e01c5818040d0b0180310510140002c0d0a1410b182c2c82c00581c1c688140d070381e290a240103840094581c0c0c3c03a0244c00400d1042c8046081c464003032880300c8800 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 551056780 1250 551055530 551055569
    0x80a03231c090519151d0102070b0108160305030d051b04030c0602010b04020f120a0e0327010809060a091b09050402040e0319030e3c0714010f030908030c04 69
    0x40d2030080d00c09407410003401c1d03c003044401715078008045000c1e00048030803450320100540c4d09a07403010b41d0031145007590340010440c1c80f009002400300403504548402c0264950b0301c49a41d02c0c0641954500074560300c1c0049403205200c64845011481ca0302550340d21682c0c0c3e0b0428030710401c002e00c03c1038099401c2105048483c44d0610840303500444143c4c0e020f00702403c0274a0400a014003c15000d0451740d6281002d500450400c05054510b80d107c1d0650b000b4444101c28490000d0349001d041e060110340400d000e400180810070310392210100b5400209003205042a07501d98801045921043c420100042910001c5410061241b40203035405d2155507d079074007495482c410001010b03c20306401000b980890305c01d03044012603000a0084441c000044414112401070072440c0c0c03480c6800010b4002501c08403031501111005030780300901902881c0c02c002c81c1440c00319080150401090781c40f0b101c021402907001c140b010f030b04030b1901612841c0a41283c007640c0c0c400c1c010f8031a100550a15400c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 551058030 1250 551056780 551056813
    0x109050705070f03030f09061104081903020a120215041a060a080c1302120106090303020f1b2116090f06080c040209220207020109080a03231c0905 65
    0x82c0481d034407000c55030740b449454908400415048000c054401c2c0c54940e02d03000704110307005080c402180008041ea8451404002d5072130074900d11b000d80041421103000350046a00400d0030b0351010b800030801004100c40100803420320079644919a003016581051006121503080390781c24001c02c09032002f01c152200c004200600d1140c2c0320b0940203501484034001d85003406062400c0000040e007015041482808507400300c44802d030080000142401c0c0d0070824180d041090fa030304131200c0c00151031258814005144100c2d0030014841c040c4a03a007001c880b101c4c1001440031049265002640c5503102c490039030f86a04501c610401083c1030512100604c02b49892003000b04035503407640144441c0c01d07110180310103500329004040e1b0000e100b1540420006418a502824501000c0f0040c3c0c0d40000380700141071050303140c1014450f6401a280400002d1300242c8800041820b00d0040c0c82641c60720500c4c00d4980720720080d681c0101208103110640d00030030340205c3e03010b0b8880c03000d5401d010003c08120 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 551059280 1250 551058030 551058037
    0x405070806150a030f0f05040201020c15070605060f04090506040302120406051b070810050613180b04020307120804051017190609020f07050601060806010203181c0b0109050705 78
    0x15900c066078611a2030410301e140c1c02424824028100817030340b008080f604208540102d11580c0e400358450b0100000c540c0e05005492414004880000110324209694903890142076002802d00c1e07602d201007402a51413181c0c08030421801841880f80f1046071a10340d1700c1d01030585040300948901c015180d6900c2c1008291401c1c1c0c0c220341c0e1201e0400b1011203e401581003142c003102c1141c0680c0c0008207101005005400d0a4401064080380a0406c00180031301788444400e10701c0110310b40408242c01200020000d00304582000304165552690300004e41040f82692141000307000e24038008042101000240c0210345040710302c0348055a0340d002c152124140004441400e000035400206000918142040403548042c03000900315100c101610403607002039801100450003041c00c1080180801029001d0451440c285403d41840d5001030743e00d000301d500c0b08500b0304012140165a80b43d000d1160b0785a0740c00b650b6240d5849080c1449440b40d1028000c1281060402c0005400140207a045 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 551060530 1250 551059280 551059291
    0x20f01030c0507030c021810060e0303040b0306010c020112023603070506070501090b281401060e03030f04120b0112030203070209042406090b0306012103170a090204050708 76
    0x24030380f42806990b42101d052850690482c1c5c001182d04072988441401440b191040e00c1c15a80c90340c1e040d040100c00f0380181c81140000b482640200030501003800700a0542e90030403800e00302001c1005040c40140c404180761200003000d0f510100d4680d01d0341421050903500b84010b190b070181c8020301441d807444290340c890a0075415034030600041009080c1100184031860103000005642003507665400c0d80503405540c03690380c844007041c82e201000200f190064a074404048200302d0303a038100354034060003c0148100b00900502ca00503000a80f41401140c04401c10100780680da81c1e102c0c81400c810807070301803058406080450000ca0140620000301001c0c43c2c140e0001c505090450b0708004010070004d0080b1284441005040501090000c403440781d40388010f804628142071070304a0b412950b80c84c80c400c1c440d520040040144e464050f0703001100201c81341c9200d40103085810240c8008580800500e8188040e1081090307104441c1d001000c402d10803034007840141c5a1040880e5141400e881c0c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 551061780 1250 551060530 551060537
    0xf03080318150a0b0906220b0102010209030105010305030a1e0e22050403020a0501110f090d0807020a0b0421030f0c031e1107050301051311010207120807020f01030c 73
    0x12903904441160245056001c0d903048034000180007154410071032042c1c4106003500c1e00e8819a01242c078001d02d0b0194055029940c01c0c0c0c2c110700403c1e4100110704401404405960f68600d0103001d030f4402c2d01126135420000d0024459542e5a240c9107030780e5800200c41b8000522044c4207281c11000f0040449a1103045507101819002c000c01003051590351281544107800240200070070710106801010b00c55800b80c0c01424522825050840c21741e28041080150b25808103c0080c101000c0c400b43c5140350b4040d00c2c500d08400d4070345080300d0141309940d0080c2d40302a41020010750030901000410035503011054105100c0407440180f5085480c41c44000c021510320140c030320346c40d4841c0003000c002c039010340391002c2c0300c01c0c1c0c01d00c0c0f050104039449100b80c0003c0001000402103407080055034001c28040d40208454030b01400c60801e040302025004021f0302c41e041204129a108110181c09440082c000607003030000d0385089506580280c00481c02840343c00c184452a41c003034414500310076103588 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 551063030 1250 551061780 551061787
    0x1109330303070b1f0b1207120501080f0d0806010c081605030f0406090801110a0302130510020c0f09011202092a0406021902060f070c0902070b0106090f030c06030b030102220f0f0308 80
    0x802d0001280300418507c1000b20000030410124418002c40703009100b0b10020b05a100d0780e190420342841d2004141d20700748602842030084a0742d003c83c00c0c02d40c0b039400c0b641c4070741c40b040e00c200c0c072642d044188640980703540b001144081600440c64002d10031180c881e16080c0105940d101d00900f40c0d080e80036071844200d002d0101844180c060b80040ca03102d010414400407035501c4000198034410016540c00040c0d00900307005c0c1143c1040008011491800c07151141191315040c5420162a98000024050494000030820f6030209484040740e0030745001c0484558080c080380c2c01180e4005104180040c401d10042400d09080c2a4009000070703005800203140042c4412050b5180e442010102c90803401c035030002480031001d10150020307a10581502032154507088004040e41301c2604040301c1c071161000c0803c002031000280c00116130a50402148511b0301100181c0203014621400f0b250070415010500303041d403410003440946d9405000d209a80740c0b06d05841c20750081c0c900008000d1300080 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 551064280 1250 551063030 551063047
    0xd3f0305060402090915010e15041a070b0106120507050c1b2d031515100306150915020111070b100b0d06031109330303070b1f0b 57
    0x2500300a501203006000540f800c03100c03030042040c0000494804001c2a41d9000100445d82e010940312401e41080f1818400c0741c1041045800074410b61242e100c0d40c881c80c1e20f00c00361200c010019100c00b160082c40e0341c0300e60f680d901005410507c3d0700c14070301036003072030240061012030054045d00d040442c4840108a03000800d58418900401c4140061744001d2000c40c202610000c2c540d0f203011311043c1c041164030341d8856414185801c0140500310785a0454000304042c00301881c5503011450350845459103503d075000b034150300a20940c0c0150802c0343c0fa1750039000c1d000d5085440c4ca4100d44042c1051451f05250400403401c03501c003e038100d4228a420010000030803480000650081c2c001f10420006a036130701200e80719580f0440503101e049889110400601654001c1f0070300c50309041d64080100c2c9414450b4860308100b05091020000e030002d6104210700c4540c0c0c1c44122414050212036403904182080c00031800708541501d80d000358030440b003030260303481c84500c01140d240724611828100b00c03 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 551065530 1250 551064280 551064287
    0x6071209261c0b03070603050c07260c0303100906050609040509010e07031203051b0f07060b03061302030c0f090118150308040518040b0601050d0b0d3f 67
    0x3038044590614109100c00c0606095004011102d0803014000044840d00c0f2824141811a00c4d4004000d0600e0501081034014900d01202c0d501c40d441080303051841c0186070242d05034580904401885d1001080c031302c5e02104000000d47c062240300d281d080c08250b0360680d0006540c1140034643e04003006000082c8582030070780013aa04015504001318800c0200c9a0315803926940c3d0748103a40c01d80d044001d10074044d4061050039042160b943c0182042200035503034005c4c600c9003488070002014002124024448198805218140000d082d200351342003d520090301c5036424007041c3c0c0300f4000c0322082c3c203131b80c0f03082c800f80b0404c0040070341b000c2040d030728003100d110030b200b40310003040384454071540d88884055044c5690006544510714140d2107031300703210030b1000b958600c0d803040741144810000c0c0700c049062070700100e901050919220307a46081c5a042c8601811400400c01c0c0c01c800111240020230030381040c0c15045100b0011a80300b40c0c11590259000300e52003d0007204181006013202c01410b20 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 551066780 1250 551065530 551065583
    0x9091a011b02120a0308040210020f030a0c051903030b0f0d0b22120c0b01050904020d02090703060909110423010504110403120e010f02010606080c13150206071209 72
    0x700700103000c0e1260040c05040c0076404e801200042c1810b000c02046151101004900030317400d100034510500003a401c260303a489900920310501c5080e11402e030800c441045082101e012003440044a144c6031315015000d80840151140304031034041c103042150602030b81810b40b141d0030a940d0283d584510340c00762078480411510058044081800c04040f82d081c004040c51042d5541d0b60070610195030420100700708040c0c200c2c2d03100e28901403e10025079035032204064440d03012a100582c03a200c1c1113040e002001c1c0c5c1d6100c491280d04000c604401c4c80f0390303962081090075094030240086502072000211000320780c1c01c903c1e85138448000501481c00e00c1d42c0300e101041c000e94480c52074540c0303d44988000d6400a031241300041d0918200c90000e5a00c43c21201c45520b072400240103030307130800202801c8200010210803100b070011440394114031034a0558001030901c0300680c4e591014404009494100488108000c20480d07078004484c3d0700c46210303d101071a04903c1541b4660000c1c03a0507501c0c0ba4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 551068030 1250 551066780 551066783
    0x10110304090e0109020d080706061205030d0c2a0b0a0513080f1e07050124031707061d0105010f050a090b010e03100b0306060907080f040512030709091a011b 69
    0x113580707a00c4040140c030740480c1d450a503030140088944904c0e2500d840c40a0b0b40d4290000d204100841a44d0400586c000082d912503400e2100082104d0340e2406045407007a070300c2102c070100c400240c100e40343e0401040c40c0880000d8042c5c0d0903020303c0d40d14881d03154190350040d40c45044c00351207990b603c000b00342c144029100000c10308800c0c62030030b000c006c140b001e00c4590090030106000c001600c070080000901c41c07002d1640c1414103503038100322000703240880d040c003601c00a49890640d180d02c0c000440e40078101d45565078810401c100c401c1d20081550814518503841080c69860400049626a0340200744401c50320000c1c40c035400c0c3d500b4101c00101410959801130f05001004561840ca50340a0004100302e02c01010700041000e018400c0519141001d00994040c420160512007e641d01409070380d4481030340ca030b8400050b2030341e19016140040d044212034005002100307011079103620841c9001158031001040c01101e85c83d039012210507054481050100720010030080b1045500d5044243e000e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 551069280 1250 551068030 551068033
    0x70806010521041a070e090601031d03040305030c0601080a120f05070b01090e12090f150c030d050105100302090102070e0a0906060306021207260415021201030210110304090e 77
    0x62200901410744010540d01113a031101041107031300342200b5010341d29610000516002500c44481b00110340f15200141119040503210603020040c2014440440301007030385001181c1e0303503698904003141c0b00e4100c5600822540540c800018030000001102c41401c0d0700300d05103845910711044251201124010100140301c014404080400e0308403546d14000c2001c440c01280800c04500d00301e0501003018461040c0c65800e010201068a580103030081d0100c0a88500e5103c4d4018068107170180102071542100f444002510410552640c0080e81210b00583d0385030f01c4504030b02c9042d010380c01110b01a81c010782c0204400c00404031040c402d59045101d52400088226081c1c5614041d00c106420030741c0c00b00c1d00010455898000482242e5000351f00340f50640d485c885000c0300031108280b00b019060101140c0012405000e464294481300e5000c0e50030031595080c010012107103640e400d00c401d0b481100210384089a5502800000810f16034074005140b03000d060408d40d03c010b1591120f0b61403123 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 551070530 1250 551069280 551069317
    0x71a090327220b040c09050f030312070905011d130b040e0d020102040e0105190e0601020309060a0819020406050d05130f0317090102120103030f0210110a080f0708060105 75
    0x1161642e202c48852180c01040307003104100d150307500741e05803628004180d001d00e00e40300c0c0304015179600400e810141e4004a4880901642c81000603256000341c43e07035005140c000c6424000305981110030030b0100c510a8a030207010750b802c1c8004020765134071030f0721080d0010101046a000088103911a60000400400004420300e040c01d600c1c0c0781036010300084001d81e500060a00240c1800d540c05c034010841200c5e5101d103050000000316400034541b04245202140d440441c00b160b000307006942038058054001c80c0c480781c10701c0006052100503100c0035089030b0b550f964911500a64006c490598507245c640034a0700c0c000103200c0000b450010a0190b0b0098000500b0b00000c00352040003560600a030381720450800066001480513102500007140c60788100890303010302c038041c0f6441d41160b4050034903040b400760890b8160306041100c04403012491806244640c20810000601541051581c0e82030680d516802001203d510503989000800c280d10300059666109d0801440700001030701000e00d4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 551071780 1250 551070530 551070607
    0xd0807020a0e0a0e15010b0a0f02070902070809090601020a0308180f0109060b09150d03030b220f0b03010b0f09040f120f030c17011404090804030602071a0903 70
    0xc4041c8255500380d000364403181c800046071000c0000c903980c07180300540c5c102554500410300125108031100c1000b405040030224002c0f9000b40115030007040298015965482145070503103040d4406a6818482c80068011550300d51000407040c1c899945521414580d440d02d00e90410000c00d400910701880c131a111402c0d0003d00d081c020380c1c2d03800f8424440401d42c40e411604024209400506444000140e00b401c03022030b40e01c8041c0c1c1420705400d410b001441c2c6031200042000e1b0807002880155070500291000368602e880d070712100b4800c0000c2c2c07040010b422000201401d03180070080840e8032002819004400e0b2070000c401c00d4000c0d100b017460011100300703544c0e11407800c011180c001c4040f900c0381c0c81e20307482aa014050903085182e540b600180c0c0805417120540202ca041c000c0c2814480840d084801c1c0342c4684c3c2c4000d2803181c02451403500d95640e0b250200207544005400c5850700039800700341c52005054203420b4042d83c00d0801841c00c103185020b8039028100000b07148040038184a030440e0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 551073030 1250 551071780 551071799
    0x105100b0313060906020301060305160801060806040f1b120204030b06040b030a0506130224031b1b0124080727060b030a0509030a02031b07030b0c0d0506060403020d0807020a 77
    0x7210184680e1780581c9a601d020f07009000ca030b81c01000340b03400050719151007411560014000741076406e0307414160001e458810205000b01640c1100070982494284011001c501124411582c0c102546c2c0701140f01000c204954140e01a074030009000c15034000104966242076000390158000244c200d5040c542540c071507920301f850076a0000c2c1d6403144884150254140549a030100c034070720003000d0442c01e49400303074407409100c0184940c400c05103140d10b14910900500440d00000f0b845154108000c000c90407250007859040a403042e1203441150600b0300081c5100c600301100d2070f46020b803c04500c2c02c0300f0044600900e0600c1c1000160101ca200500c15191180d4030103032a403184078544070b1916507041c4c030840e1006002c2040d50350007480b0b04e10806500008807038011018082142c4680c12141d2014a841c0d12a0801081282507000704551100050040c1c1960308a05005221700d440300010b05c405845180400394000d070b811220315011505200040400170700c06084031031483d035100d2540c1b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 551074280 1250 551073030 551073041
    0x40902071a13140d12090c05030d0e040506040c020a03050703030b100e040c03062103050c030c01090201021504120c080c1e07050306130201030903140f040e01080105100b031306 78
    0x72101514040d8a0070a004007443c008525031a5880184203d18040c400a810901040c0d4007458803901c83c00f00208224030312aa4a00402c40502140c95030715507002b01500d202c0079009002c1c0210301c0e010000f8041d2a09004001403c0181e030090052441d15482c00c440039031100600342c0905403202401c0300d260b10764980e0340b00d00180341d940d02020681544100000e0342d100311110f000301402c000c424060450442e562081c84142583c0c1c454003c5078070f16040e01d00d8000c1090f244145c0c0004108203518130130641009a00b64800d0382522407000082c050028213103426500a0051403201100d01146401004c5120902d07000310522420034131031001c5035140c02e580d110040403223034000d00c00310382031602080100081c00d400c074041c1849191200104081441203440a81010b88a120080034580256580c010000c101096150b03181c5078200115202c1e030040c42510388005070540002050041881210b0007681c440c500058840d04d4030340744002d140c0020f40b601c8002882ea0f04110009a11071003803 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 551075530 1250 551074280 551074291
    0xf04080919080c0108070815100309080331030519030209120a030e0312120c07020904050d0f09140f03030904060e09010b0a06051909050d030809060a11040902071a 72
    0x8090b685a0310f000100100ca0140825042c091620103020352038104c5210940c1121041c1ca201c400c1c1c003422102200038241c50200500b1000c4000b0a01980d210040080c00c800c1c1d46812002c0d86204944828445810241c1e0000e00095401d0006c01081005060100301c001e040d40b901600b04504c00d0001620b80a00081d1125541c0c400c03c11101096040081c114606404a01810100b04240895030f06d51045504000c420407203040000c0c1c902a03600241c84803a1780140c45010386c0e03c0c0620b0b007241d4401941e031520000c1004030001c81e4200d882050b501c415510340050510304808a80c09000808a0000200da8540420f00a001c21500c0358825040144441c1e055542d80341480310006003101c00d8409018007070540b00b0014012180c00c0004c4030b49460506154098840395a2002c590080c110b400040d8810402030001c000d256009551a014000000c2610000d49072503140e141101d0042c494254180018402042100600d80c05450114020741c84d180d041030b107a09203491014000c444 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 551076780 1250 551075530 551075533
    0x120114010801350c01120204121704120503270f010c021f0309020a05030a0807150f0c05030717060f0103020d0204080303040503040e010e010b0403080705420f0408091908 75
    0x2c01094a46e409003082d8002e1070301c0e00d003c42c5090305022000040c21842c0a006d08005141c614920396044d03800d08840051030f40d000d1640d04962180740060312175000b170000000d0b0142110903840d400e0340340c0c070340a0250f40c03005007140d000ca028440152100e0301c4000c0b0907a40b10145da5165500801461424504108076940c00101840d051040003103039409904118040d601c01c1c0c501030001041002180c03845508807841d00c0c401c0c00c48580d6000601090079000d0303030b454240300c40c2404054006014600446103522040000a11a40c080c00e190720b049446036404510741003c001294001d5000345419120000301518194540140ca4655407090703d04407059400050704000ea10131003c11036014015400307102203076501d041040e82c0b150007180005880710100180b92410060b04000320701c000e00010f070032031100003034142c3c0314071102629070501c20040e89a030803000402041c04a8007446804280000354a035140c030344620742a60003100302590041e10a4039840f092070040c0c03c00d880140880030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 551078030 1250 551076780 551076793
    0x1209030e101706120a12050405010908031908180a0b01090509060c03010b0904062102031e03160c0f0e09011a030a0204050912070812011401080135 65
    0x400380046070060308010402c00648444038010801030490094020408403801c201c41c40031404c040c0d08080c00450010f12144005880c0c22110707801102601c119007090f03e83c130750001e54858400e0380301d1080316440304950b85122802d24415002d00d800031b07049000c5d400b80c00c80c40000c048480d45803030940c200c2503503a0741c403640042010188600555a2101d50580a8940c1c0d0400000d14a46400b040c01000c0140501240c1c3c9001a101c5510540003003290781001c030021030349103501d46c000c038141c42c41c01d90207401031a0f250200c040c6000c01025010758180c00a61901200c500341e034111000b008001c54000202c00390000b0312020480140c005055405403111030760034004889400c643c1d2801c0c0d44c501021940e5002441564042001c541d504d0701a038010803c0c1e690044684d05000400307202d207604850101d121000d001103a009021074100707540b40005180d888000503104040807940c0c041c00514440b0040c46140d151b41d00186582440510200b0b007804548200c058075052458034032019030180 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 551079136 1106 551078030 551078057
    0x1020d110a060f1d0102040605070807080705030a0f031a060f0304050106090203011404060801112205041a010e0a0302090c0f0403060e0d02070e091c120903 69
    0x810100f15555807940c01d20000d2002d100700d20112035007084030380c5001205108440c1a01c00c603072102800c01c00302d43d403101c600c0d900500d01100c2c402c00c1444000002501000a00440542501e4038000800c00d000d0080442c0c0e0f0f010f803448801040103521000c207440c1c2d18201d034a13102c0041c030300f0fa40c1e076030b01d60421070301600066001c02c00040c40000005031403401202180c04503201204c0901a26589403c0c29003030322140200d12450400401005c5148855002840c005400080124001075a1000082d045915100e9030001400c0902e858900a42e030040d016405820101c03114407a080c115000f1620034103000b8008861104000b500040380129482618020341e802841031080b900b280c6001030300c51030134480c040058464a00085201248c440e50030307103e414072600500c10314180d200c402032046203103609181802950039050101d00203a0149203516402a00c500c048007100 = true := by decide +kernel

theorem cover : BRFrame.Cov 550899280 551079136 := by
  have h0 := BRFrame.cov_init 550899280
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550899280 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 550899280 ≤ n) (h2 : n < 551079136) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
