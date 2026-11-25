-- Prove2me | solution 1 for Formalism.E.hermitian_tensor_mul_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:23:52.468798+00:00
-- url     : https://prove2.me/submissions/1d0543ef-8b30-4bd3-9fa8-eeb1488ace55

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
theorem _root_.solution : HTmulApply := by
  intro R M₁ M₂ _ _ _ _ _ _ B₁ B₂ x₁ y₁ x₂ y₂
  simp [htmul, tensorFunctional]
end Formalism.E
