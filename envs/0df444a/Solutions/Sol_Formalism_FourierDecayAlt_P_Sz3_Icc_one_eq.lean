-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz3.Icc_one_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:32:39.395043+00:00
-- url     : https://prove2.me/submissions/b920038b-e5a3-4bff-9c27-94ae4d0ec768

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_VandermondeRatioHarmonic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz3
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz3
theorem _root_.solution (n : ℕ) : Icc 1 n = Ioc 0 n := by
  ext x; simp only [mem_Icc, mem_Ioc]; omega
end Formalism.FourierDecayAlt.P.Sz3
