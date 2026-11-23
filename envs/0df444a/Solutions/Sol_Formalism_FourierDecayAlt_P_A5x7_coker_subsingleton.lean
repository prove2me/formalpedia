-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x7.coker_subsingleton
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:31:36.409818+00:00
-- url     : https://prove2.me/submissions/f3ff0848-aaad-47c2-88ac-7c6991cd4e88

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
theorem _root_.solution {n : ℕ} {Z : Matrix (Fin n) (Fin n) K} (hZ : IsInt R Z⁻¹)
    (h1 : Z * Z⁻¹ = 1) : Subsingleton (coker R Z) := by
  rw [Submodule.Quotient.subsingleton_iff, eq_top_iff]
  intro v _
  let w : Fin n → R := fun i => ⟨(Z⁻¹ *ᵥ coeLin R v) i, mulVec_int R hZ v i⟩
  show coeLin R v ∈ LinearMap.range ((Z.mulVecLin.restrictScalars R).comp (coeLin R))
  rw [LinearMap.mem_range]
  refine ⟨w, ?_⟩
  have hw : coeLin R w = Z⁻¹ *ᵥ coeLin R v := by
    funext i
    rfl
  show Z *ᵥ coeLin R w = coeLin R v
  rw [hw, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
end Formalism.FourierDecayAlt.P.A5x7
