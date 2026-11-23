-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz5.u_mid
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:41:18.090945+00:00
-- url     : https://prove2.me/submissions/262bcb0c-3add-4d84-924b-c9bd34cf0898

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
theorem _root_.solution (c : Cfg) (de : ℕ → ℝ) (j : ℕ) (h1 : 1 ≤ j) (h2 : j + 2 ≤ c.k) :
    c.u de (j + 1) = c.v j - 1 / 2 - de j * c.Del := by
  have h0 : j ≠ 0 := by omega
  have h1' : j + 1 ≠ 1 := by omega
  have h2' : j + 1 ≠ c.k := by omega
  simp [Cfg.u, h0, h1', h2']
end Formalism.FourierDecayAlt.P.Sz5
