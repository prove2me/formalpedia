-- Prove2me | solution 1 for Formalism.HN.PlaceDecomposition.prj_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:58:22.413487+00:00
-- url     : https://prove2.me/submissions/0a851d67-61a1-4206-8e62-56429686a79b

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
theorem _root_.solution (v : P) (w : EuclideanSpace ℝ (P × ι × Fin 2)) : prj v w ∈ placePart v := by
  rw [mem_placePart]
  intro p hp
  rw [prj_apply, if_neg hp]
end Formalism.HN.PlaceDecomposition
