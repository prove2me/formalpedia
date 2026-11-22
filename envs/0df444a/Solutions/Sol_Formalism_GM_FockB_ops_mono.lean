-- Prove2me | solution 1 for Formalism.GM.FockB.ops_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:24:36.08506+00:00
-- url     : https://prove2.me/submissions/c2ebff5f-704d-44d6-98c8-2252fbecc84c

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelDecomp
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.FockB
open MvPolynomial Finset
variable {k σ : Type} [Field k]
namespace Formalism.GM.FockB
theorem _root_.solution {S S' : Set σ} (h : S ⊆ S') : Ops (k := k) S ≤ Ops S' := by
  apply Algebra.adjoin_mono
  rintro T ⟨u, hu, hT⟩
  exact ⟨u, h hu, hT⟩
end Formalism.GM.FockB
