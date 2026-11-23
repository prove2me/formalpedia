-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz4.card_mid
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:32:29.732329+00:00
-- url     : https://prove2.me/submissions/1bd1fa78-eff6-432a-9e69-e7abf5b6fb6d

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
theorem _root_.solution (c : Cfg) (hc : c.Ok) : (((Icc 2 (c.k - 1)).card : ℕ) : ℝ) = (c.k : ℝ) - 2 := by
  have hk := hc.hk
  rw [Nat.card_Icc]
  have : c.k - 1 + 1 - 2 = c.k - 2 := by omega
  rw [this, Nat.cast_sub (by omega)]; simp
end Formalism.FourierDecayAlt.P.Sz4
