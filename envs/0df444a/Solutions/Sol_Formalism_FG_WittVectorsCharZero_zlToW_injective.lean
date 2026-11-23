-- Prove2me | solution 1 for Formalism.FG.WittVectorsCharZero.zlToW_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:12.668182+00:00
-- url     : https://prove2.me/submissions/2d68d659-6f71-4da2-a98d-b4791e424365

import Definitions.Def_Formalism_FormalGroupWitt_Statement
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_WittTeichmullerRoot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.FG Formalism.FG.WittVectorsCharZero
namespace Formalism.FG.WittVectorsCharZero
theorem _root_.solution (l : ℕ) [Fact l.Prime] : Function.Injective (zlToW l) := by
  intro a b h
  have h1 := WittVector.map_injective _ (algebraMap (ZMod l) (AlgebraicClosure (ZMod l))).injective h
  exact (WittVector.equiv l).symm.injective h1
end Formalism.FG.WittVectorsCharZero
