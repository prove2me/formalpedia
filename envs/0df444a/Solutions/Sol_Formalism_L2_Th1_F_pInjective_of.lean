-- Prove2me | solution 1 for Formalism.L2.Th1.F.pInjective_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:26:20.166819+00:00
-- url     : https://prove2.me/submissions/671de95c-06fe-40b1-8090-b7ad41caad31

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaAdd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
namespace Formalism.L2.Th1.F
theorem _root_.solution (h : SigmaAdd) (hz : SigmaZero) : PInjective := by
  intro L z w hzL hwL
  have e := h L z w hzL hwL
  have hσz : wSigma L z ≠ 0 := fun h' => hzL ((hz L z).1 h')
  have hσw : wSigma L w ≠ 0 := fun h' => hwL ((hz L w).1 h')
  constructor
  · intro hP
    rw [hP, sub_self, mul_zero, neg_zero] at e
    rcases mul_eq_zero.1 e with h1 | h1
    · exact Or.inr ((hz L _).1 h1)
    · exact Or.inl ((hz L _).1 h1)
  · intro hor
    have h0 : wSigma L (z + w) * wSigma L (z - w) = 0 := by
      rcases hor with h1 | h1
      · rw [(hz L _).2 h1, mul_zero]
      · rw [(hz L _).2 h1, zero_mul]
    rw [h0] at e
    have h3 : wSigma L z ^ 2 * wSigma L w ^ 2 * (L.weierstrassP z - L.weierstrassP w) = 0 := by
      linear_combination e
    rcases mul_eq_zero.1 h3 with h1 | h1
    · exact absurd h1 (mul_ne_zero (pow_ne_zero _ hσz) (pow_ne_zero _ hσw))
    · exact sub_eq_zero.1 h1
end Formalism.L2.Th1.F
