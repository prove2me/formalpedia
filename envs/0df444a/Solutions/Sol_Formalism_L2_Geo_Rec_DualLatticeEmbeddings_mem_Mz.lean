-- Prove2me | solution 1 for Formalism.L2.Geo.Rec.DualLatticeEmbeddings.mem_Mz
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:14:13.859991+00:00
-- url     : https://prove2.me/submissions/b8c4b0ba-27bf-407f-9fbb-8710a02300b5

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
variable [StarRing K]
namespace Formalism.L2.Geo.Rec.DualLatticeEmbeddings
theorem _root_.solution (Xf : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (X : Submodule (𝓞 K) (Fin n → K))
    (z : Amb K n) : z ∈ Mz Xf X ↔ ∃ x ∈ X, Formalism.HermitianLatticesTheory.realize (Pi.basisFun K (Fin n)) Xf x = z := by
  unfold Mz Formalism.HN.zl
  show z ∈ AddSubgroup.map _ _ ↔ _
  simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup]
end Formalism.L2.Geo.Rec.DualLatticeEmbeddings
