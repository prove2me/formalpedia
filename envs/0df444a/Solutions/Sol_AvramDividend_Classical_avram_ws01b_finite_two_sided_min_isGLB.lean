-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01b_finite_two_sided_min_isGLB
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T11:23:18.441013+00:00
-- url     : https://prove2.me/submissions/a5665222-2a8c-4899-b7a1-3dafe11c6ab6

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat03_finite_extended_infimum_isGLB

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The actual finite first named two-sided exit is the GLB of all strict exit observations. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (lower upper : ℝ)
    (hfinite : min (twoSidedExitUpTime X upper ω)
        (twoSidedExitDownTime X lower ω) < ⊤) :
    IsGLB {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω}
      (min (twoSidedExitUpTime X upper ω)
        (twoSidedExitDownTime X lower ω)).toNNReal := by
  let τ : ℝ≥0∞ :=
    min (twoSidedExitUpTime X upper ω) (twoSidedExitDownTime X lower ω)
  have hτ :
      τ = ⨅ (t : ℝ≥0)
        (_ : X.X t ω < lower ∨ upper < X.X t ω), (t : ℝ≥0∞) := by
    dsimp only [τ]
    change min
      (⨅ (t : ℝ≥0) (_ : upper < X.X t ω), (t : ℝ≥0∞))
      (⨅ (t : ℝ≥0) (_ : X.X t ω < lower), (t : ℝ≥0∞)) = _
    apply le_antisymm
    · apply le_iInf
      intro t
      apply le_iInf
      intro ht
      rcases ht with hd | hu
      · exact (min_le_right _ _).trans
          (iInf_le_of_le t (iInf_le _ hd))
      · exact (min_le_left _ _).trans
          (iInf_le_of_le t (iInf_le _ hu))
    · apply le_min
      · apply le_iInf
        intro t
        apply le_iInf
        intro hu
        exact iInf_le_of_le t (iInf_le _ (Or.inr hu))
      · apply le_iInf
        intro t
        apply le_iInf
        intro hd
        exact iInf_le_of_le t (iInf_le _ (Or.inl hd))
  have hfinite' : τ ≠ ∞ := ne_of_lt hfinite
  exact chat03_finite_extended_infimum_isGLB
    (fun t : ℝ≥0 => X.X t ω < lower ∨ upper < X.X t ω)
    τ hτ hfinite'
