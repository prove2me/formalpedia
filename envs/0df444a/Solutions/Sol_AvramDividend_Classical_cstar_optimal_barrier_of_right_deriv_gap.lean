-- Prove2me | solution 1 for AvramDividend.Classical.cstar_optimal_barrier_of_right_deriv_gap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T16:44:43.929821+00:00
-- url     : https://prove2.me/submissions/f1f4809e-ed93-4e19-96e0-e31b4e0567b7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_cstar_attained_of_right_deriv_gap
import Theorems.Thm_AvramDividend_Classical_cstar_barrier_compare_of_attained_positive_minimal

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : a ∈ cstarSet W)
    (hgap : ((deriv W a : ℝ) : EReal) < derivZeroPlus W)
    (hcontDeriv : ContinuousOn (deriv W) (Set.Ioi (0 : ℝ)))
    (hpositive : 0 < deriv W (cstar W).toReal)
    (hdiff : DifferentiableOn ℝ W (Set.Ioo 0 (cstar W).toReal)) :
    cstar W < ⊤ ∧
      ∀ x b : ℝ, 0 ≤ x → x ≤ (cstar W).toReal → 0 ≤ b →
        barrierValue W b x ≤ vcstar W x := by
  have hattain : (cstar W).toReal ∈ cstarSet W :=
    cstar_attained_of_right_deriv_gap W a ha hgap hcontDeriv
  have heq : deriv W (cstar W).toReal = deriv W a :=
    le_antisymm (hattain.2 a ha.1) (ha.2 _ hattain.1)
  have hgapstar :
      ((deriv W (cstar W).toReal : ℝ) : EReal) < derivZeroPlus W := by
    rw [heq]
    exact hgap
  have hboundary : scaleDeriv W 0 = ⊤ ∨
      (scaleDeriv W 0).toReal = 0 ∨
      deriv W (cstar W).toReal ≤ (scaleDeriv W 0).toReal := by
    by_cases htop : scaleDeriv W 0 = ⊤
    · exact Or.inl htop
    · right
      right
      have hle :
          ((deriv W (cstar W).toReal : ℝ) : EReal) ≤ scaleDeriv W 0 := by
        simpa [scaleDeriv] using le_of_lt hgapstar
      have hnotbot :
          ((deriv W (cstar W).toReal : ℝ) : EReal) ≠ ⊥ := by
        simp
      have hreal := EReal.toReal_le_toReal hle hnotbot htop
      simpa using hreal
  have hcontW : ContinuousOn W (Set.Icc 0 (cstar W).toReal) :=
    hW.2.2.1.mono (by
      intro x hx
      exact hx.1)
  exact cstar_barrier_compare_of_attained_positive_minimal
    W hW.2.1 hattain hpositive hboundary hcontW hdiff
