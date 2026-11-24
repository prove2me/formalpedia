-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LieDecompositionLocal.antihermitian_part_mem_lie
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:14:21.935997+00:00
-- url     : https://prove2.me/submissions/dedb4fdf-90d4-4ff7-bd7c-d6cea9c3bd13

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliWordSumExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieDecompositionLocal
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_hpart2_lie


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LieDecompositionLocal
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5 Formalism.FourierDecayAlt.P.CapelliWordSumExpansion
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.LieDecompositionLocal
theorem _root_.solution (Z : Mat k r) : inLie k r (hpart2 (Hpk k r) Z) := Formalism.FourierDecayAlt.P.Qx2.hpart2_lie Z
end Formalism.FourierDecayAlt.P.LieDecompositionLocal
