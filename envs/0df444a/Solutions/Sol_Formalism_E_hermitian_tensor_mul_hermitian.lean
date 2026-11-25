-- Prove2me | solution 1 for Formalism.E.hermitian_tensor_mul_hermitian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:32:20.895738+00:00
-- url     : https://prove2.me/submissions/1cab5a0c-3171-4c01-bf63-0a056b7c6dde

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
theorem _root_.solution : HTmulHerm := by
  intro R M₁ M₂ _ _ _ _ _ _ B₁ B₂ h₁ h₂
  rw [LinearMap.isSymm_def] at *
  intro z w
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x₁ x₂ =>
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul y₁ y₂ =>
      simp only [htmul, tensorFunctional] at *
      simp [← h₁ x₁ y₁, ← h₂ x₂ y₂, starRingEnd_apply, mul_comm]
    | add a b ha hb => simp_all
  | add a b ha hb => simp_all
end Formalism.E
