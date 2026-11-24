-- Prove2me | solution 1 for Formalism.L2.Th1.H.cntVec_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:26:05.726983+00:00
-- url     : https://prove2.me/submissions/48f974ac-7c0f-4dc6-9e51-1f9ff43f58cb

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_TaylorMvLinear
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_IteratedDerivLine
import Theorems.Thm_Formalism_L2_Th1_H_cntVec_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
namespace Formalism.L2.Th1.H
theorem _root_.solution {n : Type*} [Fintype n] [DecidableEq n] {k : ℕ} (f : Fin k → n) :
    ∑ i, cntVec f i = k := by
  simp only [cntVec_apply]
  rw [← Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)]
  simp
end Formalism.L2.Th1.H
