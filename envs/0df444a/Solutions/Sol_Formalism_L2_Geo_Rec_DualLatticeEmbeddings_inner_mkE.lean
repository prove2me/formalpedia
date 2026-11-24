-- Prove2me | solution 1 for Formalism.L2.Geo.Rec.DualLatticeEmbeddings.inner_mkE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:10:17.033026+00:00
-- url     : https://prove2.me/submissions/ee2b3ca9-f444-445f-9076-fdaebf0fdb5d

import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_GelfandTransference_EnergyIdentity
import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_RealizationNorms_ExistsStarMulSelf
import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_RealizationNorms_SumUliftFinsetFinTwoExpand
import Theorems.Thm_Formalism_L2_Geo_Rec_DualLatticeEmbeddings_sum_ulift_finset_fin_two_expand

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
theorem _root_.solution (a c : InfinitePlace K → Fin n → ℂ) :
    inner ℝ (mkE a) (mkE c) = ∑ v, ∑ i, (star (a v i) * c v i).re := by
  simp only [mkE, PiLp.inner_apply, PiLp.toLp_apply, Fintype.sum_prod_type, sum_ulift_finset_fin_two_expand]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun i _ => ?_
  simp [Complex.mul_re]
  ring
end Formalism.L2.Geo.Rec.DualLatticeEmbeddings
