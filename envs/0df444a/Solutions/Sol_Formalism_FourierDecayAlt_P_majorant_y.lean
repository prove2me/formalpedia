-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.majorant_y
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:47:10.804609+00:00
-- url     : https://prove2.me/submissions/559c0610-cd37-481c-9f53-c70c9e5f4de9

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourierUniquenessMirabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CuspidalIrreducibleSubrep
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionDerivatives
import Theorems.Thm_Formalism_FourierDecayAlt_P_PhaseFunctionDerivatives_c_general
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_muPi_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_finrank_pi
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_muPi_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_dimension_count


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.G
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.G.MajorantY := by
  intro m E' β
  have hfr : (Module.finrank ℝ (UT (m + 2) → ℂ) : ℝ) = ((m : ℝ) + 2) * ((m : ℝ) + 1) := by
    rw [G7.finrank_pi, (dimension_count (m + 2)).1]
    push_cast [Nat.add_sub_cancel]
    simp
  have h := PhaseFunctionDerivatives.c_general (volume : Measure (UT (m + 2) → ℂ))
    ((Real.toNNReal (‖β‖ / (2 * Real.pi))) ^ Fintype.card (UT (m + 2))) E'
  rw [hfr, ← G7.muPi_eq] at h
  exact h
end Formalism.FourierDecayAlt.P
