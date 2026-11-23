-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz9.vand_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:34:26.606579+00:00
-- url     : https://prove2.me/submissions/c55d97a0-2a85-4b20-856b-df3ec2edb825

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CorollaryAOfPropositionA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_VandermondeRatioHarmonic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaBoundOnBoundary
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmRingIdempotentUnitRatioIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SixteenMulLeTwoPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz9
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz9
theorem _root_.solution (p : ℕ) (x : ℕ → ℝ) (h : ∀ s t, 1 ≤ s → s < t → t ≤ p → x t < x s) :
    0 < Vand p x := by
  unfold Vand
  apply Finset.prod_pos
  intro i hi
  apply Finset.prod_pos
  intro j hj
  rw [Finset.mem_Icc] at hi
  rw [Finset.mem_Ioc] at hj
  have hx := h i j hi.1 hj.1 hj.2
  linarith
end Formalism.FourierDecayAlt.P.Sz9
