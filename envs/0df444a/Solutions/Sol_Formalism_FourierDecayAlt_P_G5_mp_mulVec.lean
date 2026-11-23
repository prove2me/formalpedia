-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G5.mp_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:07:20.25775+00:00
-- url     : https://prove2.me/submissions/ec4dd889-16ae-490c-a76f-86e32f9f54a5

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousInvUpper
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_muPi_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_map_mulVec_volume

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
theorem _root_.solution (β : ℂ) {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (h : ‖M.det‖ = 1) :
    MeasurePreserving (fun x : ι → ℂ => M *ᵥ x) (muPi β ι) (muPi β ι) := by
  have hm : Measurable (fun x : ι → ℂ => M *ᵥ x) := (Continuous.matrix_mulVec continuous_const continuous_id).measurable
  refine ⟨hm, ?_⟩
  rw [muPi_eq, Measure.map_smul, map_mulVec_volume M h]
end Formalism.FourierDecayAlt.P.G5
