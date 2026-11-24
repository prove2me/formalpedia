-- Prove2me | solution 1 for Formalism.GM.FockB.pairwiseA
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:21:33.558246+00:00
-- url     : https://prove2.me/submissions/03d548c5-b5ce-4938-94d9-0776ea38e518

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelDecomp
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Theorems.Thm_Formalism_GM_FockB_disjA
import Theorems.Thm_Formalism_GM_FockB_nodupLA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.FockB
open MvPolynomial Finset Formalism.GM.M
variable {N r : ℕ} {D : BlockData N}
namespace Formalism.GM.FockB
theorem _root_.solution (hB : D.BlockOK) :
    (LA D).Pairwise fun a b => Disjoint (Va (wA (r := r) D) (eA D) (zA D) (sA D) a) (Va (wA D) (eA D) (zA D) (sA D) b) :=
  List.Pairwise.imp (fun hab => disjA hB hab) nodupLA
end Formalism.GM.FockB
