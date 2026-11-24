-- Prove2me | solution 1 for Formalism.L2.Geo.Rec.DualLatticeEmbeddings.norm_sq_mkE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:14:45.072354+00:00
-- url     : https://prove2.me/submissions/53640ea7-56ad-4be8-bf8a-53e4a880a210

import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_GelfandTransference_EnergyIdentity
import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_RealizationNorms_ExistsStarMulSelf
import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_RealizationNorms_SumUliftFinsetFinTwoExpand
import Theorems.Thm_Formalism_L2_Geo_Rec_DualLatticeEmbeddings_inner_mkE

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
theorem _root_.solution (c : InfinitePlace K → Fin n → ℂ) :
    ‖mkE c‖ ^ 2 = ∑ v, ∑ i, ‖c v i‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_mkE]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.mul_re]
end Formalism.L2.Geo.Rec.DualLatticeEmbeddings
