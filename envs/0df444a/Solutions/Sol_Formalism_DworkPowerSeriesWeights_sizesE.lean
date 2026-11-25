-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.sizesE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:53:37.572151+00:00
-- url     : https://prove2.me/submissions/513c3cd7-417f-42a3-8314-2a6a43487466

import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffQuadSer
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_MfactEqProdUniv
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OneRow
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FirstRowMinorDegreeLeOne
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_IntegralOperatorsOnJets
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_GaussB
import Definitions.Def_Formalism_GaussJetBounds_FinalB
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_sizesB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open Formalism Formalism.DworkPowerSeriesWeights
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution : SizesE := by
  unfold SizesE
  intro H _ _ TT c wt wt' f k b b' hf hk hb hb' hc0 hc1 hc2 hw hw'
  have hB : SizesB := sizesB
  unfold SizesB at hB
  obtain ⟨hsum, habs⟩ := hB H TT c wt wt' f k b b' hf hk hb hb' hc1 hc2 hw hw'
  have hf0 : 0 ≤ f := by
    have : (0:ℝ) ≤ (Fintype.card H : ℝ) := Nat.cast_nonneg _
    linarith
  have hC0 : 0 ≤ ∑ t, c t := Finset.sum_nonneg (fun t _ => hc0 t)
  have hT0 : (0:ℝ) ≤ (TT.card : ℝ) * b := mul_nonneg (Nat.cast_nonneg _) hb
  have hF0 : 0 ≤ f * k * b' := mul_nonneg (mul_nonneg hf0 (by linarith)) hb'
  rw [abs_le] at habs ⊢
  obtain ⟨h1, h2⟩ := habs
  constructor <;> linarith
end Formalism.DworkPowerSeriesWeights
