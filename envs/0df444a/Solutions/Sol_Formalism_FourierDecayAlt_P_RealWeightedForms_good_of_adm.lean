-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RealWeightedForms.good_of_adm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:40:21.195481+00:00
-- url     : https://prove2.me/submissions/5c290dc0-a659-4959-befe-2fbb8e8f7f96

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualKernelLemmas
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RealWeightedForms
import Theorems.Thm_Formalism_FourierDecayAlt_P_RealWeightedForms_admissible_word_pairwise_condition
import Theorems.Thm_Formalism_FourierDecayAlt_P_RealWeightedForms_regL_of_cnd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RealWeightedForms
open Finset Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.GramProductIdentities Formalism.FourierDecayAlt.P.DualKernelLemmas
open scoped Matrix
variable {S : Type}
namespace Formalism.FourierDecayAlt.P.RealWeightedForms
theorem _root_.solution {α β : ℝ} {w : List (Letter ℂ S)} (h : GrowthHypotheses α β w) : Good w := by
  refine ⟨h.1, fun l hl => ?_, (admissible_word_pairwise_condition h).imp fun hc => regL_of_cnd hc.1⟩
  rw [Complex.star_def]
  exact Complex.conj_eq_iff_im.2 (h.2.1 l hl).1
end Formalism.FourierDecayAlt.P.RealWeightedForms
