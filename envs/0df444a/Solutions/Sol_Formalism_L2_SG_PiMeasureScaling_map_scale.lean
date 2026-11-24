-- Prove2me | solution 1 for Formalism.L2.SG.PiMeasureScaling.map_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:19:29.838618+00:00
-- url     : https://prove2.me/submissions/be75baf4-ba13-4224-8ab3-a969a1bf0d16

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_PiMeasureScaling

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.PiMeasureScaling
namespace Formalism.L2.SG.PiMeasureScaling
theorem _root_.solution (s : ℂ) (hs : s ≠ 0) :
    (volume : Measure ℂ).map (fun z => s * z) = ENNReal.ofReal (Complex.normSq s)⁻¹ • volume := by
  have hdet : LinearMap.det (LinearMap.mulLeft ℝ s) = Complex.normSq s := by
    rw [← Algebra.norm_complex_apply, Algebra.norm_apply]
    rfl
  have hpos : 0 < Complex.normSq s := Complex.normSq_pos.mpr hs
  have h := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure ℂ)
    (f := LinearMap.mulLeft ℝ s) (by rw [hdet]; exact hpos.ne')
  rw [hdet, abs_of_pos (inv_pos.mpr hpos)] at h
  exact h
end Formalism.L2.SG.PiMeasureScaling
