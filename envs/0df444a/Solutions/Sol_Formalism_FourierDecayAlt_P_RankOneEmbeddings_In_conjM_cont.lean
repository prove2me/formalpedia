-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RankOneEmbeddings.In.conjM_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:26:18.590601+00:00
-- url     : https://prove2.me/submissions/a55430a1-08ae-416b-957f-000a8c28b6f0

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RankOneEmbeddings Formalism.FourierDecayAlt.P.RankOneEmbeddings.In
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
variable {k r : ℕ}
attribute [local fun_prop] mulM_meas invM_meas
namespace Formalism.FourierDecayAlt.P.RankOneEmbeddings.In
theorem _root_.solution (a : Mat k r) : Continuous (conjM a : Mt k r → Mt k r) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [conjM, Matrix.mul_apply, Matrix.of_apply]
  fun_prop
end Formalism.FourierDecayAlt.P.RankOneEmbeddings.In
