-- Prove2me | solution 1 for Formalism.E.hermitian_tensor_mul_gram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:23:54.630896+00:00
-- url     : https://prove2.me/submissions/29c2a693-7d97-4cf2-aa28-336c1199ef0f

import Definitions.Def_Formalism_FockGram_StatementTensor
import Definitions.Def_Formalism_FockGram_FockGramProofs_HermitianTensorMulHermitian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix LinearMap Module TensorProduct
noncomputable section
open Formalism Formalism.E
namespace Formalism.E
theorem _root_.solution : HTmulGram := by
  intro R M₁ M₂ ι₁ ι₂ _ _ _ _ _ _ _ _ _ _ B₁ B₂ v₁ v₂
  have h : sgram (htmul B₁ B₂) (fun p : ι₁ × ι₂ => v₁ p.1 ⊗ₜ[R] v₂ p.2) =
      Matrix.kroneckerMap (· * ·) (sgram B₁ v₁) (sgram B₂ v₂) := by
    ext ⟨i, j⟩ ⟨k, l⟩
    simp [sgram, htmul, tensorFunctional]
  refine ⟨h, ?_⟩
  rw [h]
  exact Matrix.det_kronecker _ _
end Formalism.E
