-- Prove2me | solution 1 for Formalism.HN.htImage_map_norm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:10.615648+00:00
-- url     : https://prove2.me/submissions/58c7dc8b-fff9-4936-a823-872ac128d066

import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_HarderNarasimhan_DefsPl
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_GramBlock
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtImage
import Theorems.Thm_Formalism_HN_htImageCv_map
import Theorems.Thm_Formalism_HN_htImage_map_mem
import Theorems.Thm_Formalism_HN_htImage_norm_placePart

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
theorem _root_.solution {P ι κ : Type*} [Fintype P] [Fintype ι] [Fintype κ] [DecidableEq ι]
    (M : P → Matrix κ ι ℂ) {v : P} {y : EuclideanSpace ℝ (P × ι × Fin 2)} (hy : y ∈ placePart v) :
    ‖htImageMap M y‖ ≤
      ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (M v))‖ * ‖y‖ := by
  rw [htImage_norm_placePart (htImage_map_mem M hy), htImage_norm_placePart hy, htImageCv_map]
  refine le_of_eq_of_le ?_
    ((LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (M v))).le_opNorm _)
  simp [Matrix.toEuclideanLin_apply]
end Formalism.HN
