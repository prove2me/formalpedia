-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrbitTailEstimates.integrable_long
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:28:30.049896+00:00
-- url     : https://prove2.me/submissions/b0aad509-9316-4d95-b1b5-49db04fd20eb

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitTailEstimates
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitTailEstimates_integrable_maxpow
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
open Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OrbitTailEstimates
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G2 Formalism.FourierDecayAlt.P.G7
namespace Formalism.FourierDecayAlt.P.OrbitTailEstimates
theorem _root_.solution (m : ℕ) (β : ℂ) (r : ℝ) (hr : 0 < r) :
    Integrable (fun v : UT (m + 1 + 1) → ℂ => (max 1 ‖r • v‖) ^ (-(((m : ℝ) + 1) * ((m : ℝ) + 4) + 1)))
      (muPi β (UT (m + 1 + 1))) := by
  have hfr : (Module.finrank ℝ (UT (m + 1 + 1) → ℂ) : ℝ) < ((m : ℝ) + 1) * ((m : ℝ) + 4) + 1 := by
    rw [finrank_pi, (dimension_count (m + 1 + 1)).1]
    have e : (((m + 1 + 1) * (m + 1 + 1 - 1) : ℕ) : ℝ) = ((m : ℝ) + 2) * ((m : ℝ) + 1) := by
      simp only [Nat.add_sub_cancel]; push_cast; ring
    rw [e]
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    nlinarith
  rw [muPi_eq]
  exact ((integrable_maxpow (volume : Measure (UT (m + 1 + 1) → ℂ)) _ hfr).comp_smul hr.ne').smul_measure_nnreal
end Formalism.FourierDecayAlt.P.OrbitTailEstimates
