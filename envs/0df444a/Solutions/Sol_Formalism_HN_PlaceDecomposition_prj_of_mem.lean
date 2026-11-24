-- Prove2me | solution 1 for Formalism.HN.PlaceDecomposition.prj_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:42:18.310957+00:00
-- url     : https://prove2.me/submissions/c3295a0b-f839-4927-ac48-84d1e1aeaebe

import Definitions.Def_Formalism_HarderNarasimhan_DefsPl
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Theorems.Thm_Formalism_HN_PlaceDecomposition_prj_apply
import Theorems.Thm_Formalism_HN_PlaceDecomposition_mem_placePart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
noncomputable section
open Formalism Formalism.HN
open Formalism.HN.PlaceDecomposition
variable {P ι : Type*} [Fintype P] [DecidableEq P] [Fintype ι]
namespace Formalism.HN.PlaceDecomposition
theorem _root_.solution (v : P) (w : EuclideanSpace ℝ (P × ι × Fin 2)) (hw : w ∈ placePart v) :
    prj v w = w := by
  ext p
  rw [prj_apply]
  split_ifs with h
  · rfl
  · exact ((mem_placePart v w).1 hw p h).symm
end Formalism.HN.PlaceDecomposition
