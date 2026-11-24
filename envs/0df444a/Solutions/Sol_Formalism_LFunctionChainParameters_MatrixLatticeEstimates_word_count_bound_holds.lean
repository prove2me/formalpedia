-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.MatrixLatticeEstimates.word_count_bound_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:29:28.513804+00:00
-- url     : https://prove2.me/submissions/f37b6fdf-6277-4c71-bf31-306bcbe93cd7

import Definitions.Def_Formalism_SizeWindowBrackets_FrameTraceRatioFinEquiv
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TraceConjTransposeMulSelf
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_CorollaryModelSideCondition
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_JointDModelAppliesUnitLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
open Formalism.CorankShareLayerCake.FR Formalism.HN
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.MatrixLatticeEstimates
open Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare (hsSq)
namespace Formalism.LFunctionChainParameters.MatrixLatticeEstimates
theorem _root_.solution : WordsR := by
  intro I _ ιf _ Dstar sg C0 Gam hD hsg hC hG hI hd
  have h1 : (Fintype.card I : ℝ) * (Dstar * (Gam ^ 2)⁻¹ / C0) ≤ RsG ιf := by
    unfold RsG
    calc (Fintype.card I : ℝ) * (Dstar * (Gam ^ 2)⁻¹ / C0)
        = ∑ _i : I, Dstar * (Gam ^ 2)⁻¹ / C0 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ ∑ i, (Fintype.card (ιf i) : ℝ) := Finset.sum_le_sum fun i _ => hd i
  have h2 : 0 ≤ Dstar * (Gam ^ 2)⁻¹ / C0 := by positivity
  have h3 : C0 * Gam ^ 2 / sg * (Dstar * (Gam ^ 2)⁻¹ / C0) = Dstar / sg := by
    field_simp
  calc Dstar / sg = C0 * Gam ^ 2 / sg * (Dstar * (Gam ^ 2)⁻¹ / C0) := h3.symm
    _ ≤ (Fintype.card I : ℝ) * (Dstar * (Gam ^ 2)⁻¹ / C0) := mul_le_mul_of_nonneg_right hI h2
    _ ≤ RsG ιf := h1
end Formalism.LFunctionChainParameters.MatrixLatticeEstimates
