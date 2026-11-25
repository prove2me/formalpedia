-- Prove2me | solution 1 for Formalism.L2.Geo.Rec.DualLatticeEmbeddings.discrete_Mz
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:11:11.235132+00:00
-- url     : https://prove2.me/submissions/0ee02439-83a3-4c37-b237-747ff0a3e3d2

import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_GelfandTransference_EnergyIdentity
import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_RealizationNorms_ExistsStarMulSelf
import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_RealizationNorms_SumUliftFinsetFinTwoExpand
import Theorems.Thm_Formalism_HN_place_lattice_structure


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
theorem _root_.solution (Xf : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (hXf : ∀ v, IsUnit (Xf v).det)
    (X : Submodule (𝓞 K) (Fin n → K)) (hfg : X.FG) : DiscreteTopology (Mz Xf X) :=
  (Formalism.HN.place_lattice_structure K (Fin n → K) (Fin n) (Pi.basisFun K (Fin n)) Xf hXf X hfg).1.2
end Formalism.L2.Geo.Rec.DualLatticeEmbeddings
