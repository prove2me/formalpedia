-- Prove2me | solution 1 for Formalism.HN.htImage_map_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:49:03.4177+00:00
-- url     : https://prove2.me/submissions/b1a33d36-6a29-4feb-b581-f5c89fad3a5e

import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_HarderNarasimhan_DefsPl
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_GramBlock
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtImage
import Theorems.Thm_Formalism_HN_mem_place_part_iff
import Theorems.Thm_Formalism_HN_htImageCv_zero_of_mem

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
theorem _root_.solution {P ι κ : Type*} [Fintype P] [Fintype ι] [Fintype κ]
    (M : P → Matrix κ ι ℂ) {v : P} {y : EuclideanSpace ℝ (P × ι × Fin 2)} (hy : y ∈ placePart v) :
    htImageMap M y ∈ placePart v := by
  rw [mem_place_part_iff]
  intro p hp
  have h0 : htImageCv y p.1 = 0 := htImageCv_zero_of_mem hp hy
  simp [htImageMap, h0]
end Formalism.HN
