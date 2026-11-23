-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G7.jacobian
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:17:21.200782+00:00
-- url     : https://prove2.me/submissions/fbe6ae71-5bac-45ae-a763-22628fae6af4

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_mp_shear
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_map_scale

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G7
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G2
namespace Formalism.FourierDecayAlt.P.G7
theorem _root_.solution (n : ℕ) (β t : ℂ) (ht : t ≠ 0) :
    Measure.map (coordMap n t) (muBlock β n) = Real.toNNReal ((‖t‖ ^ (n * (n + 3)))⁻¹) • muBlock β n := by
  have e : coordMap n t = (fun p : BlockCoord n => ((t • p.1, t • p.2.1, t • p.2.2) : BlockCoord n)) ∘
      (fun p : BlockCoord n => ((p.1 ᵥ* (wMat n * upper p.2.1), p.2) : BlockCoord n)) := rfl
  have hm : Measurable (fun p : BlockCoord n => ((t • p.1, t • p.2.1, t • p.2.2) : BlockCoord n)) := by
    fun_prop
  rw [e, ← Measure.map_map hm (mp_shear β n).measurable, (mp_shear β n).map_eq, map_scale β t n ht]
end Formalism.FourierDecayAlt.P.G7
