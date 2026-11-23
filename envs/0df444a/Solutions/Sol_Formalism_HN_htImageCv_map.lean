-- Prove2me | solution 1 for Formalism.HN.htImageCv_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:56:44.610949+00:00
-- url     : https://prove2.me/submissions/cbae1566-3dae-40ab-9070-4d2b558a179a

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
theorem _root_.solution {P ι κ : Type*} [Fintype P] [Fintype ι] [Fintype κ] (M : P → Matrix κ ι ℂ)
    (y : EuclideanSpace ℝ (P × ι × Fin 2)) (v : P) :
    htImageCv (htImageMap M y) v = (M v).mulVec (htImageCv y v) := by
  funext i
  apply Complex.ext <;> simp [htImageCv, htImageMap]
end Formalism.HN
