-- Prove2me | solution 1 for Formalism.REAL.genExp_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:05:02.137974+00:00
-- url     : https://prove2.me/submissions/2b382405-25b0-4fd9-b2a6-dc16a672bb07

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnGVIff
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IndefiniteUnitaryPreservesForm
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CompactExponentialSurjective
import Theorems.Thm_Formalism_REAL_polar_decomposition_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped Matrix.Norms.L2Operator
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution (h : KExp) : GenExp := by
  intro n ε g hg
  obtain ⟨k, X, hk, hX, rfl⟩ := (polar_decomposition_holds n ε).1 g hg
  obtain ⟨Z, hZ, hZk, -⟩ := h n ε k hk
  exact ⟨Z, X, hZ, hX, by rw [hZk]⟩
end Formalism.REAL
