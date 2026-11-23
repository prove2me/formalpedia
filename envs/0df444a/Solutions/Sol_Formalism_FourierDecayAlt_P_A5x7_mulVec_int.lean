-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x7.mulVec_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:28:04.353338+00:00
-- url     : https://prove2.me/submissions/608703bb-0c3a-4ea5-a49d-24aad37ae96a

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsIntOfLatOfLe
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsOpenIsIntSet
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x7
variable {K : Type} [CommRing K] (R : Subring K)
namespace Formalism.FourierDecayAlt.P.A5x7
theorem _root_.solution {n : ℕ} {A : Matrix (Fin n) (Fin n) K} (hA : IsInt R A) (v : Fin n → R)
    (j : Fin n) : (A *ᵥ coeLin R v) j ∈ R := by
  show (∑ i, A j i * coeLin R v i) ∈ R
  refine Subring.sum_mem _ (fun i _ => Subring.mul_mem _ (hA j i) ?_)
  exact (v i).2
end Formalism.FourierDecayAlt.P.A5x7
