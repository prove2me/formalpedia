-- Prove2me | solution 1 for Formalism.L2.Th1.F.sigma_product_locally_uniform
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:52:46.163904+00:00
-- url     : https://prove2.me/submissions/33c7e15a-87cf-4020-91a0-38062e1fae11

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Legendre
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaConv
import Theorems.Thm_Formalism_L2_Th1_F_SigmaConv_norm_wFactor_sub_one_le
import Theorems.Thm_Formalism_L2_Th1_F_SigmaConv_summable_majorant
import Theorems.Thm_Formalism_L2_Th1_F_SigmaConv_eventually_large
import Theorems.Thm_Formalism_L2_Th1_F_SigmaConv_continuous_wFactor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Filter
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open SigmaConv
namespace Formalism.L2.Th1.F
theorem _root_.solution : SigmaProdLU := by
  intro L
  have key : HasProdLocallyUniformlyOn (fun (l : L.lattice) (z : ℂ) => 1 + (wFactor (l : ℂ) z - 1))
      (fun z => ∏' l : L.lattice, (1 + (wFactor (l : ℂ) z - 1))) Set.univ := by
    rw [HasProdLocallyUniformlyOn, tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ]
    intro K _ hK
    obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall 0
    refine HasProdUniformlyOn.tendstoUniformlyOn <| Summable.hasProdUniformlyOn_one_add (f := fun (l : L.lattice) (z : ℂ) => wFactor (l : ℂ) z - 1)
      hK (summable_majorant L r) ?_ ?_
    · filter_upwards [eventually_large L (2 * r)] with l hl x hx
      exact norm_wFactor_sub_one_le r l x (by simpa using hr hx) hl
    · intro l
      exact ((continuous_wFactor _).sub continuous_const).continuousOn
  simpa only [add_sub_cancel] using key
end Formalism.L2.Th1.F
