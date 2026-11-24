-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.threshold_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:04:41.00321+00:00
-- url     : https://prove2.me/submissions/20be59c5-de0c-4e3c-9c48-35f2ecdbd800

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SupremumAIsMajorant
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx5_lambda_threshold_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx5_lamPrimeSq_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx5_supA_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped Pointwise
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Jx5
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : ThresholdsMonotone := by
  intro ι _ G C C' de de' T T' l hC h hg hv hI b s w
  have hκ : 0 ≤ 2 * Real.pi / G.g := by positivity
  have hN : 0 ≤ G.N := by unfold Sz.Glob.N; positivity
  have h1 := lambda_threshold_mono G.m b s hC h hκ hN hI.le
    (supA_nonneg G de de' T T' l (decide (b = 1 ∧ s = 1)) w hg hv)
  refine ⟨h1.1, h1.2, Real.sqrt_nonneg _, Real.sqrt_le_sqrt ?_⟩
  exact lamPrimeSq_mono G.m b hC h hκ hN hI.le (supA_nonneg G de de' T T' l false w hg hv)
end Formalism.FourierDecayAlt.P
