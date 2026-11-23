-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.mem_initSet
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:24.492482+00:00
-- url     : https://prove2.me/submissions/b42c3be8-6164-4c7e-885f-9796bde30c0e

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_IntegralMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SecondEmbeddingInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (N i : ℕ) (k : Fin N) : k ∈ initSet N i ↔ k.val < i := by
  simp [initSet]
end Formalism.MainNotions.PlaneGram
