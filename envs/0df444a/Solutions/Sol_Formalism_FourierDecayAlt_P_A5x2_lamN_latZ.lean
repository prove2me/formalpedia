-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x2.lamN_latZ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:01:33.994932+00:00
-- url     : https://prove2.me/submissions/1a2a659a-7ff1-4b48-b822-79b07494b4eb

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x2_lamTil_fin
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x2_lamN_big

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x2
open Formalism.DoubleCosetMeasures.P Formalism.DoubleCosetMeasures.P.Phase
variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ}
namespace Formalism.FourierDecayAlt.P.A5x2
theorem _root_.solution (Z : Matrix (Fin n) (Fin n) K) (hZ : IsUnit Z.det) (l : ℕ) :
    latZ R Z ≤ LinearMap.ker (lamN R Z l) := by
  intro v hv
  obtain ⟨y, hy⟩ := (mem_latZ R Z v).1 hv
  rw [LinearMap.mem_ker]
  by_cases hl : l < n
  · show Submodule.Quotient.mk (lamTil R Z (⟨l, hl⟩ : Fin n).val v) = 0
    rw [lamTil_fin, ← hy, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hZ, Matrix.one_mulVec,
      Submodule.Quotient.mk_eq_zero, coeLin_apply]
    exact ⟨y ⟨l, hl⟩, rfl⟩
  · rw [lamN_big R Z l (by omega)]; rfl
end Formalism.FourierDecayAlt.P.A5x2
