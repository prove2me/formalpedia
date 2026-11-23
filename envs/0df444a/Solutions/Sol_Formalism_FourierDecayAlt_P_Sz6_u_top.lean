-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz6.u_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:41:32.975066+00:00
-- url     : https://prove2.me/submissions/2bb5c097-ffc9-4a79-8313-332c70736485

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaFactorisation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.Sz Finset
open Formalism.FourierDecayAlt.P.Sz6
namespace Formalism.FourierDecayAlt.P.Sz6
theorem _root_.solution (c : Cfg) (de : ℕ → ℝ) (i : ℕ) (hi : 1 ≤ i) (ht : c.top = true)
    (hk : i + 1 = c.k) : c.u de (i + 1) = -c.bp := by
  have n1 : ¬ (i + 1 = 1) := by omega
  simp only [Cfg.u, if_neg n1, if_pos hk, Cfg.ulast, if_pos ht]
end Formalism.FourierDecayAlt.P.Sz6
