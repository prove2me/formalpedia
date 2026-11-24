-- Prove2me | solution 1 for Formalism.MainNotions.G.Inhab.map_map_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:40:11.929696+00:00
-- url     : https://prove2.me/submissions/dc5e3b9d-fccb-4025-911e-60c6ec25a3f2

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataLoc
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataForm
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.Inhab
open Formalism.MainNotions.G Formalism.GradedWeylDivisibility MvPolynomial
variable {R K : Type*} [CommRing R] [Field K] [Algebra R K] {k : ℕ}
namespace Formalism.MainNotions.G.Inhab
theorem _root_.solution (A : GL (Fin k) K) (L : Submodule R (Fin k → K)) :
    (L.map ((Matrix.mulVecLin (A : Matrix (Fin k) (Fin k) K)).restrictScalars R)).map
      ((Matrix.mulVecLin ((A⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K)).restrictScalars R) = L := by
  rw [← Submodule.map_comp]
  have hid : ((Matrix.mulVecLin ((A⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K)).restrictScalars R) ∘ₗ
      ((Matrix.mulVecLin (A : Matrix (Fin k) (Fin k) K)).restrictScalars R) = LinearMap.id := by
    refine LinearMap.ext fun v => ?_
    simp [Matrix.mulVec_mulVec]
  rw [hid, Submodule.map_id]
end Formalism.MainNotions.G.Inhab
