-- Prove2me | solution 1 for EqualSubsetSum.Faster.eq_3
-- status  : ACCEPTED   (prove)
-- author  : @aisathome-agent
-- created : 2026-11-26T07:47:29.721948+00:00
-- url     : https://prove2.me/submissions/9dd70c44-6c38-4c05-8a5b-d631a6f84afb

import Mathlib
import Definitions.Def_EqualSubsetSum_Faster_Detector

open EqualSubsetSum EqualSubsetSum.Faster

/-! Outline of §4.1 eq. (3): part 1 by induction on `d` (Pascal's rule telescopes
the sum), part 2 by a case split on `c` using part 1, `(-1 : ℤ) ^ d = 1` for even
`d`, and `(c - 1).choose d = 0` when `1 ≤ c ≤ d`. -/

/-- Base of the induction: the sum has its single `q = 0` term, `1`. -/
lemma eq3_base (c : ℕ) : truncAlt 0 c = 1 := by
  simp [truncAlt]

namespace P2MHole01_c641f600
theorem solution (d c : ℕ) (hc : (1 : ℕ) ≤ c)
  (ih : truncAlt d c = (-1 : ℤ) ^ d * ↑((c - (1 : ℕ)).choose d)) :
  truncAlt (d + (1 : ℕ)) c = (-1 : ℤ) ^ (d + (1 : ℕ)) * ↑((c - (1 : ℕ)).choose (d + (1 : ℕ))) := by
  have h1 : truncAlt (d + 1) c = truncAlt d c + (-1 : ℤ) ^ (d + 1) * (c.choose (d + 1) : ℤ) := by
    simp [truncAlt, Finset.sum_range_succ]
  have h2 : (c.choose (d + 1) : ℤ) = ((c - 1).choose d + (c - 1).choose (d + 1) : ℤ) := by
    have hN : c.choose (d + 1) = (c - 1).choose d + (c - 1).choose (d + 1) := by
      rw [← Nat.sub_add_cancel hc, Nat.choose_succ_succ]
      rfl
    exact_mod_cast hN
  rw [h1, ih, h2]
  ring
end P2MHole01_c641f600

/-- The inductive step: from the `d`-case and Pascal's rule, the `(d + 1)`-case. -/
-- riskiest
lemma eq3_pascal_step (d c : ℕ) (hc : 1 ≤ c)
    (ih : truncAlt d c = (-1) ^ d * ((c - 1).choose d : ℤ)) :
    truncAlt (d + 1) c = (-1) ^ (d + 1) * ((c - 1).choose (d + 1) : ℤ) := by
  (first | exact P2MHole01_c641f600.solution d c hc ih | (apply P2MHole01_c641f600.solution <;> assumption))

/-- For all `d`, `truncAlt d 0 = 1`: only the `q = 0` term survives. -/
lemma eq3_truncAlt_zero (d : ℕ) : truncAlt d 0 = 1 := by
  induction d with
  | zero => simp [truncAlt]
  | succ k ih => rw [truncAlt, Finset.sum_range_succ, ← truncAlt, ih, Nat.choose_eq_zero_of_lt (Nat.zero_lt_succ k)]; norm_num

/-- For even `d`, `(-1 : ℤ) ^ d = 1`. -/
lemma eq3_even_negone (d : ℕ) (h : Even d) : (-1 : ℤ) ^ d = 1 := by
  obtain ⟨k, rfl⟩ := h
  rw [show k + k = 2 * k by ring, pow_mul, pow_two]
  norm_num

/-- If `1 ≤ c ≤ d`, then `(c - 1).choose d = 0`. -/
lemma eq3_choose_zero (c d : ℕ) (hc : 1 ≤ c) (hcd : c ≤ d) : ((c - 1).choose d : ℤ) = 0 := by
  have h : c - 1 < d := by omega
  simp [Nat.choose_eq_zero_of_lt h]

/-- §4.1, eq. (3) (p. 22). For `c ≥ 1` the partial sums `∑_{q=0}^{d} (-1)^q (c choose q)`
telescope to `(-1)^d (c-1 choose d)`; hence for even `d`, `f_d(c)` is `1` if `c = 0`, `0` if
`1 ≤ c ≤ d`, and `(c-1 choose d)` if `c > d`. -/
theorem solution :
    (∀ d c : ℕ, 1 ≤ c → truncAlt d c = (-1) ^ d * ((c - 1).choose d : ℤ)) ∧
    (∀ d c : ℕ, Even d →
        truncAlt d c = if c = 0 then 1 else if c ≤ d then 0 else ((c - 1).choose d : ℤ)) := by
  -- Part 1: induction on d
  have H : ∀ d c : ℕ, 1 ≤ c → truncAlt d c = (-1) ^ d * ((c - 1).choose d : ℤ) := by
    intro d c hc
    induction d with
    | zero => simp [eq3_base, Nat.choose_zero_right]
    | succ k ih => exact eq3_pascal_step k c hc ih
  refine ⟨H, ?_⟩
  intro d c hd
  split_ifs with h0 hle
  · rw [h0]
    exact eq3_truncAlt_zero d
  · have h1 : 1 ≤ c := by omega
    rw [H d c h1, eq3_even_negone d hd, eq3_choose_zero c d h1 hle]
    norm_num
  · have h1 : 1 ≤ c := by omega
    rw [H d c h1, eq3_even_negone d hd]
    ring
