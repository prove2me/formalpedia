-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G5.map_mulVec_volume
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:19.523894+00:00
-- url     : https://prove2.me/submissions/3b4a7357-1169-4bc8-a528-d953e15d4ed2

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousInvUpper

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
set_option linter.unusedSimpArgs false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G5
open Formalism.FourierDecayAlt.G
namespace Formalism.FourierDecayAlt.P.G5
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (h : ‖M.det‖ = 1) :
    Measure.map (fun x : ι → ℂ => M *ᵥ x) volume = volume := by
  have hdet : LinearMap.det ((Matrix.toLin' M).restrictScalars ℝ) = 1 := by
    rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply,
      Complex.normSq_eq_norm_sq, h, one_pow]
  have h2 := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (ι → ℂ))
    (f := (Matrix.toLin' M).restrictScalars ℝ) (by rw [hdet]; exact one_ne_zero)
  rw [hdet] at h2
  have h3 : Measure.map (fun x : ι → ℂ => M *ᵥ x) volume = ENNReal.ofReal |(1 : ℝ)⁻¹| • volume := h2
  simpa using h3
end Formalism.FourierDecayAlt.P.G5
