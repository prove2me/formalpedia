-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz5.glCard_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:41:15.388602+00:00
-- url     : https://prove2.me/submissions/1e722964-e8d8-4981-9959-b7064caf74f5

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MassRatioFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CorollaryAOfPropositionA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CriticalThresholdLowerBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz5
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz5
theorem _root_.solution (p : ℕ) (q : ℝ) (hq : 1 < q) : 0 < glCard p q := by
  unfold glCard
  apply Finset.prod_pos
  intro j hj
  rw [Finset.mem_range] at hj
  have h1 : q ^ j < q ^ p := by
    first
    | exact pow_lt_pow_right₀ hq hj
    | exact pow_lt_pow_right hq hj
    | gcongr
  linarith
end Formalism.FourierDecayAlt.P.Sz5
