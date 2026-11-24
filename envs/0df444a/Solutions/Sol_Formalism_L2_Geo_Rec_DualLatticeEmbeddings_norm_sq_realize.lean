-- Prove2me | solution 1 for Formalism.L2.Geo.Rec.DualLatticeEmbeddings.norm_sq_realize
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:22:03.766862+00:00
-- url     : https://prove2.me/submissions/f8f62d22-69ae-4677-bbda-781d9c07be20

import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_GelfandTransference_EnergyIdentity
import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_RealizationNorms_ExistsStarMulSelf
import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_RealizationNorms_SumUliftFinsetFinTwoExpand
import Theorems.Thm_Formalism_L2_Geo_Rec_DualLatticeEmbeddings_norm_sq_mkE
import Theorems.Thm_Formalism_L2_Geo_Rec_DualLatticeEmbeddings_realize_eq

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
open NumberField NumberField.InfinitePlace Module Matrix
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Geo Formalism.L2.Geo.Rec Formalism.L2.Geo.Rec.DualLatticeEmbeddings
variable {K : Type} [Field K] [NumberField K] {n : ℕ} [StarRing K] [IsTotallyComplex K]
namespace Formalism.L2.Geo.Rec.DualLatticeEmbeddings
theorem _root_.solution (Xf : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (x : Fin n → K) :
    ‖Formalism.HermitianLatticesTheory.realize (Pi.basisFun K (Fin n)) Xf x‖ ^ 2 = ∑ v, ∑ i, ‖fc Xf v x i‖ ^ 2 := by
  rw [realize_eq, norm_sq_mkE]
end Formalism.L2.Geo.Rec.DualLatticeEmbeddings
