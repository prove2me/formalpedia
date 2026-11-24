-- Prove2me | solution 1 for Formalism.L2.Col.chiSymF_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:54:13.660427+00:00
-- url     : https://prove2.me/submissions/aa143825-acf3-4f13-a6d9-3373fa4610d3

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
variable (κ)
variable {κ}
variable {K : Type} [Field K]
namespace Formalism.L2.Col
theorem _root_.solution (ψ : AddChar κ K) (n k rS : ℕ) (M : ↥(HPsymF κ n k rS)) :
    chiSymF ψ n k rS M = chiSym ψ n k rS ⟨toSymOrd κ n k rS M.1, M.2⟩ := rfl
end Formalism.L2.Col
