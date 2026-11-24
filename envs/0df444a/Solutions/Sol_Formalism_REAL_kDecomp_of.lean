-- Prove2me | solution 1 for Formalism.REAL.kDecomp_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:56:35.221051+00:00
-- url     : https://prove2.me/submissions/56743d29-9e5e-4077-b7a1-0c55351cf0b5

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IsCompactInvariantOrthogonalInf
import Theorems.Thm_Formalism_REAL_compactDecomposition_of_finrank

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution (he : KHiExist) (ho : KOrth) : KDecomp := by
  intro V _ _ n ε F S hfin hr hu hS
  exact compactDecomposition_of_finrank he V n ε F hr hu _ S rfl hfin hS
end Formalism.REAL
