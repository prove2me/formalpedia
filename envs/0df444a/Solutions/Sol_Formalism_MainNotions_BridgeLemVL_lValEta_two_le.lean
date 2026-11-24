-- Prove2me | solution 1 for Formalism.MainNotions.BridgeLemVL.lValEta_two_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:59:11.486132+00:00
-- url     : https://prove2.me/submissions/5d9e4953-3935-4661-bb97-a1ccbb0fc532

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_MassRatioBound
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_EulerFacMulConjInvSplit
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLemVL
import Theorems.Thm_Formalism_MainNotions_BridgeLemVL_sum_resChar_le
import Theorems.Thm_Formalism_MainNotions_BridgeLemVL_eulerFac_two_le
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_eulerFac_pos
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_multipliable_eulerFac


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLemVL
open NumberField Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.IdealNormInequalities
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.MainNotions.BridgeLemVL
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) :
    Formalism.HermitianLatticesTheory.lValEta K 2 ≤ Real.exp (2 * ((Module.finrank ℚ K : ℝ) * Z2)) := by
  unfold Formalism.HermitianLatticesTheory.lValEta
  refine (multipliable_eulerFac hK 2 le_rfl).tprod_le_of_prod_le fun s => ?_
  calc ∏ P ∈ s, Formalism.HermitianLatticesTheory.eulerFac K 2 P.1
      ≤ ∏ P ∈ s, Real.exp (2 * ((resChar P.1 : ℝ) ^ 2)⁻¹) :=
        Finset.prod_le_prod (fun P _ => (eulerFac_pos hK P.2 2 (by norm_num)).le)
          (fun P _ => eulerFac_two_le hK P.2)
    _ = Real.exp (2 * ∑ P ∈ s, ((resChar P.1 : ℝ) ^ 2)⁻¹) := by
        rw [← Real.exp_sum, Finset.mul_sum]
    _ ≤ Real.exp (2 * ((Module.finrank ℚ K : ℝ) * Z2)) :=
        Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (sum_resChar_le s) (by norm_num))
end Formalism.MainNotions.BridgeLemVL
