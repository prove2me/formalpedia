-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.edgeW_swap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:05:44.498208+00:00
-- url     : https://prove2.me/submissions/48768e71-33ed-4665-a4df-391d3b636371

import Definitions.Def_Formalism_GaussJetBounds_StatementN
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffQuadSer
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_edgeW_swap_lt

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
variable {n : ℕ}
variable {R : Type u} [CommRing R]
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution (w : Fin n → Fin n → R) (hw : ∀ i j, w i j = w j i) {a b : Fin n} (hab : a ≠ b)
    {τ : Equiv.Perm (Fin n)} (hτa : τ a = a) (hτb : τ b = b) :
    edgeW w (Equiv.swap a b * τ) = w a b * edgeW w τ := by
  rcases lt_or_gt_of_ne hab with h | h
  · exact edgeW_swap_lt w h hτa hτb
  · rw [Equiv.swap_comm, hw a b]
    exact edgeW_swap_lt w h hτb hτa
end Formalism.DworkPowerSeriesWeights
