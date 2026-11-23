-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz6.Icc_one_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:32:40.216998+00:00
-- url     : https://prove2.me/submissions/6f72ee13-5e56-48c3-a25b-710dde4918c7

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
theorem _root_.solution (n : ℕ) : Icc 1 n = Ico 1 (n + 1) := by
  ext x; simp only [mem_Icc, mem_Ico]; omega
end Formalism.FourierDecayAlt.P.Sz6
