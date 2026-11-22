-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz4.u_last
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:00:20.168902+00:00
-- url     : https://prove2.me/submissions/bf134eb6-6a53-46b4-9ff5-6c239c62ea15

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
theorem _root_.solution (c : Cfg) (de : ℕ → ℝ) (hc : c.Ok) : c.u de c.k = c.ulast := by
  have : c.k ≠ 1 := by have := hc.hk; omega
  simp [Cfg.u, this]
end Formalism.FourierDecayAlt.P.Sz4
