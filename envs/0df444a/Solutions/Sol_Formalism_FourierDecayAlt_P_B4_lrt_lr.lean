-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B4.lrt_lr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:27:48.612835+00:00
-- url     : https://prove2.me/submissions/aa6e9150-7d78-4683-8e97-26753e24ee94

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.B4
theorem _root_.solution (u v : List (Mat k r)) : LRt ((lr u v).map Prod.fst) := by
  refine ⟨u.length, v.length, ?_⟩
  first
    | (simp [lr, Function.comp_def]; done)
    | (simp [lr, Function.comp_def, List.map_const']; done)
    | (simp [lr, List.map_map, Function.comp_def, List.eq_replicate_iff]; done)
end Formalism.FourierDecayAlt.P.B4
