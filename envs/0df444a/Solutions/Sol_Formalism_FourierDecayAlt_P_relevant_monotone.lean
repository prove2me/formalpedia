-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.relevant_monotone
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:15:22.331394+00:00
-- url     : https://prove2.me/submissions/3203d6cd-6bf8-469b-83c5-d2e2f22a365b

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerAntidiagonalExact
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerFourthCondition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RelevantMonotoneOfParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_relevant_criterion
import Theorems.Thm_Formalism_FourierDecayAlt_P_c2x4_stab_sum_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_relevant_pair_criterion
import Theorems.Thm_Formalism_FourierDecayAlt_P_relevant_trivial_case


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
open C2x4
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C2.RelevantMono := by
  intro m w d c hd hc
  rw [← relevant_criterion m w d]
  constructor
  · intro hall a b hab hwab
    rw [← relevant_trivial_case m w d c hd hc a b hab hwab]
    intro x
    obtain ⟨h1, h2, h3, h4⟩ := relevant_pair_criterion m w d hd a b hab hwab x
    rw [← h4]
    exact hall _ h1 _ h2 h3
  · intro hC l hl u' hu he
    rw [c2x4_stab_sum_zero w d hd hC l u' hl hu he]
    simp [C2.psiC]
end Formalism.FourierDecayAlt.P
