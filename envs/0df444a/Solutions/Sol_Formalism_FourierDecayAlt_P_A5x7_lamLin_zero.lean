-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x7.lamLin_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:31:36.420231+00:00
-- url     : https://prove2.me/submissions/bcbf776a-c3aa-4385-971b-46324c55ffe9

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsIntOfLatOfLe
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsOpenIsIntSet
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x7_mulVec_int

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
theorem _root_.solution {n : ℕ} {Z : Matrix (Fin n) (Fin n) K} (hZ : IsInt R Z⁻¹) (v : Fin n → R) :
    lamLin R Z v = 0 := by
  have hmem : lastCoord R (Z⁻¹ *ᵥ coeLin R v) ∈ R := by
    unfold lastCoord
    rw [LinearMap.sum_apply]
    refine Subring.sum_mem _ (fun j _ => ?_)
    split_ifs
    · exact mulVec_int R hZ v j
    · exact R.zero_mem
  show Submodule.Quotient.mk (lastCoord R (Z⁻¹ *ᵥ coeLin R v)) = 0
  rw [Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
  exact ⟨⟨_, hmem⟩, rfl⟩
end Formalism.FourierDecayAlt.P.A5x7
