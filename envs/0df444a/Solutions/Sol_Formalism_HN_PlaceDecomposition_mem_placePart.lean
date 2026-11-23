-- Prove2me | solution 1 for Formalism.HN.PlaceDecomposition.mem_placePart
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:55:55.661747+00:00
-- url     : https://prove2.me/submissions/bc9e161b-ed70-4c43-a288-00209536a744

import Definitions.Def_Formalism_HarderNarasimhan_DefsPl
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit

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
theorem _root_.solution (v : P) (w : EuclideanSpace ℝ (P × ι × Fin 2)) :
    w ∈ placePart v ↔ ∀ p : P × ι × Fin 2, p.1 ≠ v → w p = 0 := by
  first
    | exact Iff.rfl
    | simp [placePart]
    | (unfold placePart; simp)
end Formalism.HN.PlaceDecomposition
