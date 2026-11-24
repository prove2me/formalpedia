-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RealWeightedForms.admissible_word_pairwise_condition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:22:34.216596+00:00
-- url     : https://prove2.me/submissions/b6c9107b-75bf-4b22-b8b0-324787748305

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualKernelLemmas
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RealWeightedForms

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
theorem _root_.solution {α β : ℝ} {w : List (Letter ℂ S)} (h : GrowthHypotheses α β w) :
    w.Pairwise (fun l l' => Cnd l l' ∧ Cnd l' l) := by
  rw [List.pairwise_iff_get]
  intro i j hij
  exact ⟨h.2.2 i j (ne_of_lt hij), h.2.2 j i (ne_of_lt hij).symm⟩
end Formalism.FourierDecayAlt.P.RealWeightedForms
