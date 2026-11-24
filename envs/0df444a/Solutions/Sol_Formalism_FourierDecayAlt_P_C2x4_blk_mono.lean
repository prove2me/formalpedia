-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.C2x4.blk_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:36:24.916816+00:00
-- url     : https://prove2.me/submissions/0f3340c9-75ee-4dff-85ef-fedb98d0a85a

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerAntidiagonalExact
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerFourthCondition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RelevantMonotoneOfParts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.C2x4
variable {m : ℕ}
namespace Formalism.FourierDecayAlt.P.C2x4
theorem _root_.solution (w : Equiv.Perm (Fin m)) : Monotone (blk w) := by
  intro a b hab
  unfold blk
  apply Finset.card_le_card
  intro c hc
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
  exact ⟨lt_of_lt_of_le hc.1 hab, hc.2⟩
end Formalism.FourierDecayAlt.P.C2x4
