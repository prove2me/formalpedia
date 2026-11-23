-- Prove2me | solution 1 for Formalism.L2.Geo.Rec.DualLatticeEmbeddings.realize_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:22:29.416261+00:00
-- url     : https://prove2.me/submissions/5c0480f7-8622-4cc4-b6d4-d39af81e6c3a

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
variable [StarRing K]
namespace Formalism.L2.Geo.Rec.DualLatticeEmbeddings
theorem _root_.solution (Xf : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (x : Fin n → K) :
    Formalism.HermitianLatticesTheory.realize (Pi.basisFun K (Fin n)) Xf x = mkE (fun v => fc Xf v x) := by
  ext p
  have h : Formalism.HermitianLatticesTheory.vecAt (Pi.basisFun K (Fin n)) p.1 x = fun i => p.1.embedding (x i) := by
    funext i
    unfold Formalism.HermitianLatticesTheory.vecAt
    simp
  simp [Formalism.HermitianLatticesTheory.realize, Formalism.HermitianLatticesTheory.realizeRaw, Formalism.HermitianLatticesTheory.fcoord, mkE, fc, h]
end Formalism.L2.Geo.Rec.DualLatticeEmbeddings
