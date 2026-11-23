-- Prove2me | solution 1 for DiscrNeWork.discr_ne_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:28:45.972076+00:00
-- url     : https://prove2.me/submissions/8603f629-7838-4b74-a99b-80b9d7c6d7cf

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DiscrNe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NonzeroDiscriminants_DiscLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NonzeroDiscriminants_DiscMain
import Theorems.Thm_DiscrNeWork_discr_scaled

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
theorem _root_.solution (w₁ w₂ : ℂ) (h : 0 < ((starRingEnd ℂ) w₁ * w₂).im) :
    PI.discr (PI.lat2 w₁ w₂) ≠ 0 := by
  have hw : w₁ ≠ 0 := by
    rintro rfl
    simp at h
  have hτ : 0 < (w₂ / w₁).im := by
    have e : (w₂ / w₁).im = ((starRingEnd ℂ) w₁ * w₂).im / Complex.normSq w₁ := by
      rw [Complex.div_im]
      simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
      ring
    rw [e]
    exact div_pos h (Complex.normSq_pos.mpr hw)
  have h3 := discr_scaled w₁ hw ⟨w₂ / w₁, hτ⟩
  rwa [show w₁ * ((⟨w₂ / w₁, hτ⟩ : UpperHalfPlane) : ℂ) = w₂ by
    rw [UpperHalfPlane.coe_mk]
    field_simp] at h3
end DiscrNeWork
