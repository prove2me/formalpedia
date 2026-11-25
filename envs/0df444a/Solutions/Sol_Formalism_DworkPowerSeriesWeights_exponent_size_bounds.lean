-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.exponent_size_bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:39:29.249004+00:00
-- url     : https://prove2.me/submissions/a77e4885-480c-4047-ae2d-149b4de842c1

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementQ
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffQuadSer
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OneRow
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_IntegralOperatorsOnJets
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_base_size_bounds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u
open Formalism Formalism.DworkPowerSeriesWeights
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution : SizesE := by
  intro H _ _ TT c wt wt' f k b b' hf hk hb hb' hc0 hc1 hc2 hwt hwt'
  obtain ⟨h1, h2⟩ := base_size_bounds H TT c wt wt' f k b b' hf hk hb hb' hc1 hc2 hwt hwt'
  have h3 : 0 ≤ ∑ t, c t := Finset.sum_nonneg fun t _ => hc0 t
  have h4 : |(1 / 2) * ∑ t, c t| ≤ (TT.card : ℝ) * b + f * k * b' := by
    rw [abs_of_nonneg (by positivity)]
    linarith
  refine (abs_add_le _ _).trans ?_
  linarith
end Formalism.DworkPowerSeriesWeights
