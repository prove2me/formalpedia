-- Prove2me | solution 1 for Formalism.GM.FockB.nodupLA
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:14:45.431772+00:00
-- url     : https://prove2.me/submissions/0ef83328-5c1f-4bc7-ade6-ad8472343ab3

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
open MvPolynomial Finset Formalism.GM.M
variable {N r : ℕ} {D : BlockData N}
namespace Formalism.GM.FockB
theorem _root_.solution : (LA D).Nodup := by
  simp only [LA, List.nodup_cons, List.mem_map, reduceCtorEq, and_false, exists_false, not_false_eq_true,
    true_and]
  exact (List.nodup_finRange _).map (Option.some_injective _)
end Formalism.GM.FockB
