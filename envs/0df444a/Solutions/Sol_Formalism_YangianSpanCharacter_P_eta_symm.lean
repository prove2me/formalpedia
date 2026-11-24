-- Prove2me | solution 1 for Formalism.YangianSpanCharacter.P.eta_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:42:18.515925+00:00
-- url     : https://prove2.me/submissions/0d102b68-5a02-4ed6-b2a8-693aa258681b

import Definitions.Def_Formalism_YangianSpanCharacter_StatementY
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRTTProofs_DiagonalEntryEqOfModularRelation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.YangianSpanCharacter Formalism.YangianSpanCharacter.P
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y
variable {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A] {t : 𝕜 → Matrix (Fin 2) (Fin 2) A}
  {τinv : 𝕜 → A} {q : 𝕜 → 𝕜} {S : Set 𝕜}
namespace Formalism.YangianSpanCharacter.P
theorem _root_.solution (u v : 𝕜) : eta t τinv v u = eta t τinv u v := by
  simp only [eta]
  rw [← neg_sub u v, inv_neg, neg_smul, ← smul_neg, neg_sub]
end Formalism.YangianSpanCharacter.P
