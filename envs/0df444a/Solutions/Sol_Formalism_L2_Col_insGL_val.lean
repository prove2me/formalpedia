-- Prove2me | solution 1 for Formalism.L2.Col.insGL_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:08:24.209874+00:00
-- url     : https://prove2.me/submissions/05a42c0e-7775-4791-98b3-0a68af9168a4

import Definitions.Def_Formalism_LocalToGlobal_Columns_GenericUnipotentCharacter
import Definitions.Def_Formalism_LocalToGlobal_Columns_LevGSym

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.L2 Formalism.L2.Col
variable (κ : Type) [CommRing κ]
variable {κ}
namespace Formalism.L2.Col
theorem _root_.solution (N c k N' : ℕ) (hk : k ≤ N) (hN : N' = N + c) (A : GL (Fin N) κ) (a b : Fin N') :
    ((insGL κ N c k N' hk hN A : GL (Fin N') κ) : Matrix (Fin N') (Fin N') κ) a b =
      Matrix.fromBlocks (A : Matrix (Fin N) (Fin N) κ) 0 0 1 (insEquiv N c k N' hk hN a) (insEquiv N c k N' hk hN b) := rfl
end Formalism.L2.Col
