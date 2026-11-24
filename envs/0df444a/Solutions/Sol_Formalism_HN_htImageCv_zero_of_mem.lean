-- Prove2me | solution 1 for Formalism.HN.htImageCv_zero_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:27.462427+00:00
-- url     : https://prove2.me/submissions/3b43a905-9b04-439d-a298-400127db305d

import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_HarderNarasimhan_DefsPl
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_GramBlock
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtImage
import Theorems.Thm_Formalism_HN_mem_place_part_iff

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
theorem _root_.solution {P ι : Type*} [Fintype P] [Fintype ι] {v w : P} (h : w ≠ v)
    {y : EuclideanSpace ℝ (P × ι × Fin 2)} (hy : y ∈ placePart v) : htImageCv y w = 0 := by
  rw [mem_place_part_iff] at hy
  funext i
  apply Complex.ext
  · simpa [htImageCv] using hy (w, i, 0) h
  · simpa [htImageCv] using hy (w, i, 1) h
end Formalism.HN
