-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz4.vand_succ_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:32:40.068625+00:00
-- url     : https://prove2.me/submissions/d6bb83db-30d1-4600-9122-7500926e3d69

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz4
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz4
theorem _root_.solution (p : ℕ) (x : ℕ → ℝ) :
    Vand (p + 1) x = Vand p x * ∏ i ∈ Icc 1 p, (x i - x (p + 1)) := by
  unfold Vand
  rw [Finset.prod_Icc_succ_top (by omega), Finset.Ioc_self, Finset.prod_empty, mul_one,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Finset.prod_Ioc_succ_top (mem_Icc.mp hi).2]
end Formalism.FourierDecayAlt.P.Sz4
