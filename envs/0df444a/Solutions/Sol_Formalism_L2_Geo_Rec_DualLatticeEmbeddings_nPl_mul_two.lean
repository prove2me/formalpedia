-- Prove2me | solution 1 for Formalism.L2.Geo.Rec.DualLatticeEmbeddings.nPl_mul_two
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:14:14.108459+00:00
-- url     : https://prove2.me/submissions/bedb067f-80a7-4ed4-b2d5-5ae62663ae3f

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
open NumberField NumberField.InfinitePlace Module Matrix
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Geo Formalism.L2.Geo.Rec Formalism.L2.Geo.Rec.DualLatticeEmbeddings
variable {K : Type} [Field K] [NumberField K] {n : ℕ}
namespace Formalism.L2.Geo.Rec.DualLatticeEmbeddings
theorem _root_.solution [IsTotallyComplex K] : Fintype.card (InfinitePlace K) * 2 = finrank ℚ K := by
  rw [NumberField.IsTotallyComplex.finrank, NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    NumberField.IsTotallyComplex.nrRealPlaces_eq_zero]
  ring
end Formalism.L2.Geo.Rec.DualLatticeEmbeddings
