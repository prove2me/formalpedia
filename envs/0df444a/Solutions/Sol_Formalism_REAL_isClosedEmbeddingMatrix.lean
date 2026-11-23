-- Prove2me | solution 1 for Formalism.REAL.isClosedEmbeddingMatrix
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:16:51.079191+00:00
-- url     : https://prove2.me/submissions/bc4e74bf-4c35-42fc-93af-9f3d9cbe5daa

import Definitions.Def_Formalism_RealPlaceAnalysis_UJLocCompact
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsInducingCoeMatrix
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_KoszulLowersPower
import Theorems.Thm_Formalism_REAL_isClosed_pseudoUnitary
import Theorems.Thm_Formalism_REAL_range_coeMatrix
import Theorems.Thm_Formalism_REAL_isInducing_coeMatrix
import Theorems.Thm_Formalism_REAL_injective_coeMatrix
import Theorems.Thm_UpperTheory_Reformulated_B_Qk27_isInducing_coeMatrix


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
theorem _root_.solution : UJEmb := by
  intro n ε
  refine ⟨⟨⟨isInducing_coeMatrix ε, injective_coeMatrix ε⟩, ?_⟩, range_coeMatrix ε⟩
  show IsClosed (Set.range (coeMatrixAlt ε))
  rw [range_coeMatrix ε]
  exact isClosed_pseudoUnitary ε
end Formalism.REAL
