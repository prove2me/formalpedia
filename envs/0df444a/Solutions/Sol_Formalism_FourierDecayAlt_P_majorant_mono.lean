-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.majorant_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:56:45.937856+00:00
-- url     : https://prove2.me/submissions/8f717769-9a11-4600-90fb-cf87491575e7

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SupremumAIsMajorant

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
theorem _root_.solution : MajMono := by
  intro E W _ D ρ ρ' l h hav
  unfold TB.Data.maj
  apply Finset.prod_le_prod
  · intro v _
    exact le_min zero_le_one (pow_nonneg (div_nonneg (h v).1 (hav v)) _)
  · intro v _
    apply min_le_min le_rfl
    exact pow_le_pow_left₀ (div_nonneg (h v).1 (hav v)) (div_le_div_of_nonneg_right (h v).2 (hav v)) _
end Formalism.FourierDecayAlt.P
