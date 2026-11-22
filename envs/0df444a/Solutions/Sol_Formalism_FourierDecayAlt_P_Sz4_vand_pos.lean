-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz4.vand_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:24:14.947518+00:00
-- url     : https://prove2.me/submissions/f1e473f0-c441-4c1c-b808-07b69fa73ffb

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
theorem _root_.solution (p : ℕ) (x : ℕ → ℝ) (h : ∀ i j : ℕ, 1 ≤ i → i < j → j ≤ p → x j < x i) :
    0 < Vand p x := by
  unfold Vand
  refine Finset.prod_pos fun i hi => Finset.prod_pos fun j hj => ?_
  have := h i j (mem_Icc.mp hi).1 (mem_Ioc.mp hj).1 (mem_Ioc.mp hj).2
  linarith
end Formalism.FourierDecayAlt.P.Sz4
