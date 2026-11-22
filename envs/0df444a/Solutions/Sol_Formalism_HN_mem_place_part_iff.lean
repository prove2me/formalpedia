-- Prove2me | solution 1 for Formalism.HN.mem_place_part_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T17:38:47.90769+00:00
-- url     : https://prove2.me/submissions/1c54ca10-787e-4a6a-ad39-7525d54fd9e4

import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_HarderNarasimhan_DefsPl
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_GramBlock
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtImage

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.HN
namespace Formalism.HN
theorem _root_.solution {P ι : Type*} [Fintype P] [Fintype ι] {v : P}
    {x : EuclideanSpace ℝ (P × ι × Fin 2)} :
    x ∈ placePart v ↔ ∀ p : P × ι × Fin 2, p.1 ≠ v → x p = 0 := by
  simp [placePart, Submodule.mem_iInf]
end Formalism.HN
