-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.norm_wirtL_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:53:34.533937+00:00
-- url     : https://prove2.me/submissions/914f0cc6-1eb9-489f-b066-0610a8e5a64c

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WirtingerIntegrationByParts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
open Formalism.FourierDecayAlt.G MeasureTheory
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {d : ℕ}
namespace Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
theorem _root_.solution (k : Fin d) : ‖wirtL V k‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun T => ?_
  have h1 : ‖T (Pi.single k (1 : ℂ))‖ ≤ ‖T‖ := by
    refine (T.le_opNorm _).trans ?_
    rw [Pi.norm_single]; simp
  have h2 : ‖T (Pi.single k Complex.I)‖ ≤ ‖T‖ := by
    refine (T.le_opNorm _).trans ?_
    rw [Pi.norm_single]; simp
  have : wirtL V k T = (1 / 2 : ℂ) • (T (Pi.single k 1) - Complex.I • T (Pi.single k Complex.I)) := by
    simp [wirtL]
  rw [this, norm_smul]
  have h3 : ‖T (Pi.single k 1) - Complex.I • T (Pi.single k Complex.I)‖ ≤ ‖T‖ + ‖T‖ := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, Complex.norm_I, one_mul]
    exact add_le_add h1 h2
  have h4 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  rw [h4]; linarith
end Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
