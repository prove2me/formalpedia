-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.inverse_last_column_formula
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:51:21.821799+00:00
-- url     : https://prove2.me/submissions/0543b3c3-a077-4187-b825-d3fa3094584d

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x2_blk_app
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x2_revIn_app
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x2_inv_last
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_up_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val



set_option autoImplicit false
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A5x2 Formalism.DoubleCosetMeasures.P Formalism.DoubleCosetMeasures.P.Phase
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.A5.InvLastCol := by
  intro K _ h s t hs x y hx hy a b c hb hc
  have hsum : (addBlock h s t).1.sum = h.1.sum + s := by simp [addBlock]
  have hrc : revF (addBlock h s t).1 c = b := by
    apply Fin.ext
    rw [revF_val, hc]
    show revIn (h.1 ++ [s]) h.1.sum = b.val
    rw [revIn_app _ _ hs]; omega
  have hblk : (addBlock h s t).2 (blk (addBlock h s t).1 c) = t := by
    rw [hc]
    show Function.update h.2 h.1.length t (blk (h.1 ++ [s]) h.1.sum) = t
    rw [blk_app _ _ hs, Function.update_self]
  have hyi := isUpUni_inv K hy
  have key : ∀ a', (x * pt (addBlock h s t).1 (addBlock h s t).2 * y)⁻¹ a' b
      = ((t⁻¹ : Kˣ) : K) * y⁻¹ a' c := by
    intro a'
    rw [inv_last _ _ x y hx hy a' b c hb hrc, hblk]
  refine ⟨key a, fun hca => ?_, ?_⟩
  · rw [key a, up_zero hyi hca, mul_zero]
  · rw [key c, hyi.2 c, mul_one]
end Formalism.FourierDecayAlt.P
