-- Prove2me | solution 1 for Formalism.MainNotions.G.GLWeightTheory.sourceVar_fst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:21:41.034405+00:00
-- url     : https://prove2.me/submissions/a08ff54f-befd-42fe-9ebb-e388a47953f5

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_RootWeights_TwistSubEqMatrixSubst
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_RootWeights_MatrixSubstTransvectionX

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
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory
open Formalism.MainNotions.G
namespace Formalism.MainNotions.G.GLWeightTheory
theorem _root_.solution {ι : Type*} {n : ℕ} (LL : Letters ι) (a b : Fin n) (l : ι) : (sourceVar LL a b l).1 = l := by
  unfold sourceVar
  split_ifs <;> rfl
end Formalism.MainNotions.G.GLWeightTheory
