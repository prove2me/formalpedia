-- Prove2me | solution 1 for Formalism.L2.Th1.A.Q2.norm_le_one_of_monic_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:27:49.493337+00:00
-- url     : https://prove2.me/submissions/a30596fe-0eb1-4ba1-ba87-5a41c05a9401

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementQ
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowDouble
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_NormLeOneOfMonicTwo
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_hb


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u v
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.Q2
variable {K : Type} [NormedField K] [IsUltrametricDist K]
namespace Formalism.L2.Th1.A.Q2
theorem _root_.solution {y b c : K} (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1)
    (h : y ^ 2 + b * y = c) : ‖y‖ ≤ 1 := by
  by_contra hy
  push_neg at hy
  have h2 : y ^ 2 = c + -(b * y) := by rw [← h]; ring
  have h3 : ‖y ^ 2‖ ≤ max ‖c‖ ‖-(b * y)‖ := by
    rw [h2]
    exact IsUltrametricDist.norm_add_le_max _ _
  rw [norm_neg, norm_pow, norm_mul] at h3
  have hby : ‖b‖ * ‖y‖ ≤ ‖y‖ := by nlinarith [norm_nonneg b, norm_nonneg y]
  have hmax : max ‖c‖ (‖b‖ * ‖y‖) ≤ ‖y‖ := max_le (by linarith) hby
  nlinarith
end Formalism.L2.Th1.A.Q2
