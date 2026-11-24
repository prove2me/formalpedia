-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x5.heisConjLevMeas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:42:45.901739+00:00
-- url     : https://prove2.me/submissions/23f2de0d-7cac-4ef3-aa72-dc0cb934ae98

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_heisConjLev
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_B2x5_map__Heis_fdf4803780e5
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_measurable_conjM
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_shear
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_measurePreserving_GV

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace Formalism.FourierDecayAlt.P.B2x5
theorem _root_.solution : HeisConjLevMeas := by
  intro k r' g hg
  refine map_μHeis k r' (measurable_conjM _)
    (shear k r' (c := fun _ => (0 : ℝ)) (measurePreserving_GV hg) measurable_const) ?_
  intro y
  show ιLev k 1 r' g * heis0 k r' y * (ιLev k 1 r' g)⁻¹ = heis0 k r' (g *ᵥ y.1, y.2 + 0)
  rw [heisConjLev k r' g hg y, add_zero]
end Formalism.FourierDecayAlt.P.B2x5
