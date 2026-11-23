-- Prove2me | solution 1 for DiscrNeWork.discrNe_all
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:34:39.870163+00:00
-- url     : https://prove2.me/submissions/ccd33ceb-6067-4de0-9e70-e83cfa9336f9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DiscrNe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NonzeroDiscriminants_DiscLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NonzeroDiscriminants_DiscMain
import Theorems.Thm_DiscrNeWork_discr_ne_of_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ModularForm EisensteinSeries UpperHalfPlane
noncomputable section
open DiscrNeWork
namespace DiscrNeWork
theorem _root_.solution : PI.DiscrNe := by
  intro w₁ w₂ h
  rcases lt_or_gt_of_ne h with hlt | hgt
  · have h2 : 0 < ((starRingEnd ℂ) w₂ * w₁).im := by
      have e : ((starRingEnd ℂ) w₂ * w₁).im = -((starRingEnd ℂ) w₁ * w₂).im := by
        simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
        ring
      linarith
    have hswap : PI.lat2 w₁ w₂ = PI.lat2 w₂ w₁ := by
      unfold PI.lat2
      rw [Set.pair_comm]
    rw [hswap]
    exact discr_ne_of_pos w₂ w₁ h2
  · exact discr_ne_of_pos w₁ w₂ hgt
end DiscrNeWork
