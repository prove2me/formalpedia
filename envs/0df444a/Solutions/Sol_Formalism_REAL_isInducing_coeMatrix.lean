-- Prove2me | solution 1 for Formalism.REAL.isInducing_coeMatrix
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:11:45.374523+00:00
-- url     : https://prove2.me/submissions/3b06b12a-36b7-4a34-9c3f-1ec56d223cd1

import Definitions.Def_Formalism_RealPlaceAnalysis_UJLocCompact
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsInducingCoeMatrix
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_KoszulLowersPower
import Theorems.Thm_Formalism_REAL_coeMatrix_inv_eq
import Theorems.Thm_Formalism_REAL_continuous_coeMatrix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Topology
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) : IsInducing (coeMatrixAlt ε) := by
  have hc : Continuous (fun M : Matrix (Fin n) (Fin n) ℂ =>
      (M, MulOpposite.op (Jm ε * Mᴴ * Jm ε))) :=
    continuous_id.prodMk (MulOpposite.continuous_op.comp
      ((continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const))
  refine IsInducing.of_comp (continuous_coeMatrix ε) hc ?_
  have heq : (fun M : Matrix (Fin n) (Fin n) ℂ => (M, MulOpposite.op (Jm ε * Mᴴ * Jm ε))) ∘ coeMatrixAlt ε
      = (Units.embedProduct (Matrix (Fin n) (Fin n) ℂ)) ∘ (Subtype.val : UJ ε → _) := by
    funext g
    refine Prod.ext rfl ?_
    show MulOpposite.op (Jm ε * (coeMatrixAlt ε g)ᴴ * Jm ε) =
      MulOpposite.op (((g : (Matrix (Fin n) (Fin n) ℂ)ˣ)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
        Matrix (Fin n) (Fin n) ℂ)
    rw [coeMatrix_inv_eq]
  rw [heq]
  exact Units.isInducing_embedProduct.comp IsInducing.subtypeVal
end Formalism.REAL
