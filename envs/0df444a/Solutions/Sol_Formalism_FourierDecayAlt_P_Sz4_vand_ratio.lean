-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz4.vand_ratio
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:39:58.416246+00:00
-- url     : https://prove2.me/submissions/cbf58b42-6d6f-497a-8f07-64372dd4e464

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
theorem _root_.solution (p : ℕ) (x y : ℕ → ℝ) (r : ℕ → ℕ → ℝ)
    (h : ∀ i j : ℕ, 1 ≤ i → i < j → j ≤ p → x i - x j = r i j * (y i - y j)) :
    Vand p x = (∏ i ∈ Icc 1 p, ∏ j ∈ Ioc i p, r i j) * Vand p y := by
  unfold Vand
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j hj => ?_
  exact h i j (mem_Icc.mp hi).1 (mem_Ioc.mp hj).1 (mem_Ioc.mp hj).2
end Formalism.FourierDecayAlt.P.Sz4
