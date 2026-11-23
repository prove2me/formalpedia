-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G5.mp_add_const
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:20.134104+00:00
-- url     : https://prove2.me/submissions/c3307b04-ab42-4b1c-a1e6-f9dd0dca2b4f

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousInvUpper
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_muPi_eq

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
theorem _root_.solution (β : ℂ) {ι : Type} [Fintype ι] (c : ι → ℂ) :
    MeasurePreserving (fun x : ι → ℂ => x + c) (muPi β ι) (muPi β ι) := by
  refine ⟨measurable_add_const c, ?_⟩
  rw [muPi_eq, Measure.map_smul, map_add_right_eq_self]
end Formalism.FourierDecayAlt.P.G5
