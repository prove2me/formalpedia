-- Prove2me | solution 1 for Formalism.L2.Geo.Rec.DualLatticeEmbeddings.finrank_amb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:02:20.81243+00:00
-- url     : https://prove2.me/submissions/2f8aebf8-0c16-4bf0-9890-86d159fe1513

import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_GelfandTransference_EnergyIdentity
import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_RealizationNorms_ExistsStarMulSelf
import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_RealizationNorms_SumUliftFinsetFinTwoExpand
import Theorems.Thm_Formalism_L2_Geo_Rec_DualLatticeEmbeddings_nPl_mul_two

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.InfinitePlace Module Matrix
noncomputable section
open NumberField NumberField.InfinitePlace Module Matrix
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Geo Formalism.L2.Geo.Rec Formalism.L2.Geo.Rec.DualLatticeEmbeddings
variable {K : Type} [Field K] [NumberField K] {n : ℕ}
namespace Formalism.L2.Geo.Rec.DualLatticeEmbeddings
theorem _root_.solution [IsTotallyComplex K] : finrank ℝ (Amb K n) = finrank ℚ K * n := by
  rw [finrank_euclideanSpace, Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
    ← nPl_mul_two]
  ring
end Formalism.L2.Geo.Rec.DualLatticeEmbeddings
