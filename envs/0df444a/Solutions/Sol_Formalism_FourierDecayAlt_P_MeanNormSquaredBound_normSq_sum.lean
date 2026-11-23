-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.MeanNormSquaredBound.normSq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:26:41.793451+00:00
-- url     : https://prove2.me/submissions/a3ac0c48-676a-4250-a6ec-e25ed534d83b

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MeanNormSquaredBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_MeanNormSquaredBound_inner_sum_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.MeanNormSquaredBound
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.MeanNormSquaredBound
theorem _root_.solution {ι : Type} (S : Finset ι) (c : ι → ℂ) (v : ι → E) :
    ((‖∑ i ∈ S, c i • v i‖ ^ 2 : ℝ) : ℂ) =
      ∑ i ∈ S, ∑ j ∈ S, c i * conj (c j) * inner ℂ (v j) (v i) := by
  rw [← inner_sum_sum, inner_self_eq_norm_sq_to_K]
  push_cast
  rfl
end Formalism.FourierDecayAlt.P.MeanNormSquaredBound
