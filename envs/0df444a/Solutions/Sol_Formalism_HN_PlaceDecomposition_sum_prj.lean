-- Prove2me | solution 1 for Formalism.HN.PlaceDecomposition.sum_prj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:55:56.468069+00:00
-- url     : https://prove2.me/submissions/e4b20f6d-06b1-4818-8d56-a0a8079b5071

import Definitions.Def_Formalism_HarderNarasimhan_DefsPl
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Theorems.Thm_Formalism_HN_PlaceDecomposition_prj_apply

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
theorem _root_.solution (w : EuclideanSpace ℝ (P × ι × Fin 2)) : ∑ v, prj v w = w := by
  ext p
  first
    | rw [Finset.sum_apply]
    | erw [Finset.sum_apply]
    | simp only [WithLp.ofLp_sum, Finset.sum_apply]
  simp [prj_apply]
end Formalism.HN.PlaceDecomposition
