-- Prove2me | solution 1 for Formalism.GM.FockB.ops_commute
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:09.739036+00:00
-- url     : https://prove2.me/submissions/fcfb0201-728c-4d38-ac30-6460e677fd65

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelDecomp
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Theorems.Thm_Formalism_GM_FockB_atoms_commute

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
theorem _root_.solution {S S' : Set σ} (hS : Disjoint S S') {T T' : Module.End k (MvPolynomial σ k)}
    (hT : T ∈ Ops S) (hT' : T' ∈ Ops S') : Commute T T' := by
  refine Algebra.commute_of_mem_adjoin_of_forall_mem_commute hT' (fun b hb => ?_)
  exact (Algebra.commute_of_mem_adjoin_of_forall_mem_commute hT
    (fun a ha => (atoms_commute hS ha hb).symm)).symm
end Formalism.GM.FockB
