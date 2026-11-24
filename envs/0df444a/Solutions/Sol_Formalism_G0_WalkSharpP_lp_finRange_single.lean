-- Prove2me | solution 1 for Formalism.G0.WalkSharpP.lp_finRange_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:19:37.51954+00:00
-- url     : https://prove2.me/submissions/c6b0bd58-7d4c-4155-95fc-51e61e5ca1eb

import Definitions.Def_Formalism_SubspaceCounting_Statement
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_WalkSharp
import Theorems.Thm_Formalism_G0_WalkSharpP_lp_single

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0
open Formalism.G0.WalkSharpP
variable {R X : Type} [CommRing R] [AddCommGroup X] [Module R X] {V : ℕ}
namespace Formalism.G0.WalkSharpP
theorem _root_.solution (y : Fin V → Module.End R X) (v : Fin V) :
    lp y (List.finRange V) (fun u => if u = v then 1 else 0) = y v := by

  rw [lp_single y v _ (List.nodup_finRange V), if_pos (List.mem_finRange v)]
end Formalism.G0.WalkSharpP
