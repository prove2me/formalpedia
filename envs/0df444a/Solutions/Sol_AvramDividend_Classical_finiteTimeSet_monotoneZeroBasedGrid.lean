-- Prove2me | solution 1 for AvramDividend.Classical.finiteTimeSet_monotoneZeroBasedGrid
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T10:40:33.509632+00:00
-- url     : https://prove2.me/submissions/ef191bfe-560c-4b8c-a22e-98c3ca7190fd

import Mathlib.Probability.Independence.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Probability.IdentDistrib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open scoped NNReal ENNReal
theorem solution (J : Finset ℝ≥0) :
    ∃ (n : ℕ) (t : ℕ → ℝ≥0) (e : J → Fin n),
      Monotone t ∧ t 0 = 0 ∧
      ∀ j : J, t ((e j).val + 1) = (j : ℝ≥0) := by
  classical
  let g := J.orderEmbOfFin rfl
  let f : ℕ → ℝ≥0 := fun k => if h : k < J.card then g ⟨k, h⟩ else J.sup id
  have hf : Monotone f := by
    refine monotone_nat_of_le_succ fun k => ?_
    by_cases h1 : k + 1 < J.card
    · have h0 : k < J.card := by omega
      simp only [f, dif_pos h0, dif_pos h1]
      exact g.monotone (Fin.mk_le_mk.2 (Nat.le_succ k))
    · by_cases h0 : k < J.card
      · simp only [f, dif_pos h0, dif_neg h1]
        exact Finset.le_sup (f := id) (J.orderEmbOfFin_mem rfl _)
      · simp only [f, dif_neg h0, dif_neg h1, le_refl]
  let t : ℕ → ℝ≥0 := fun k => Nat.casesOn k 0 f
  refine ⟨J.card, t, fun j => (J.orderIsoOfFin rfl).symm j, ?_, rfl, ?_⟩
  · refine monotone_nat_of_le_succ fun k => ?_
    cases k with
    | zero => exact bot_le
    | succ k => exact hf (Nat.le_succ k)
  · intro j
    show f _ = _
    simp only [f, Fin.is_lt, dif_pos]
    have := congrArg Subtype.val ((J.orderIsoOfFin rfl).apply_symm_apply j)
    rw [Finset.coe_orderIsoOfFin_apply] at this
    exact this
