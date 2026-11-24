-- Prove2me | solution 1 for Formalism.L2.Geo.Rec.DualLatticeEmbeddings.sum_ulift_finset_fin_two_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:02:17.909798+00:00
-- url     : https://prove2.me/submissions/c08b7f71-a045-4439-a4f0-a213047e0dac

import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_GelfandTransference_EnergyIdentity
import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_RealizationNorms_ExistsStarMulSelf
import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_RealizationNorms_SumUliftFinsetFinTwoExpand

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
open Formalism Formalism.L2 Formalism.L2.Geo Formalism.L2.Geo.Rec Formalism.L2.Geo.Rec.DualLatticeEmbeddings
variable {K : Type} [Field K] [NumberField K] {n : ℕ}
namespace Formalism.L2.Geo.Rec.DualLatticeEmbeddings
theorem _root_.solution (g : Fin 2 → ℝ) : ∑ k, g k = g 0 + g 1 := Fin.sum_univ_two g
end Formalism.L2.Geo.Rec.DualLatticeEmbeddings
