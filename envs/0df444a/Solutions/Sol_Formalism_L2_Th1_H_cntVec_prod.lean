-- Prove2me | solution 1 for Formalism.L2.Th1.H.cntVec_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:26:21.181063+00:00
-- url     : https://prove2.me/submissions/e0b95eb0-cc95-46b1-9aed-b2f386da8989

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
theorem _root_.solution {n : Type*} [Fintype n] [DecidableEq n] {k : ℕ} {K : Type*} [CommMonoid K] (v : n → K)
    (f : Fin k → n) : ∏ i, v i ^ cntVec f i = ∏ j, v (f j) := by
  rw [← Finset.prod_fiberwise Finset.univ f (fun j => v (f j))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [cntVec_apply, ← Finset.prod_const]
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [(Finset.mem_filter.1 hj).2]
end Formalism.L2.Th1.H
