-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.gaussian_hessian_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:48:34.783887+00:00
-- url     : https://prove2.me/submissions/15cfe04a-4617-4e8a-95ba-a8fbb551ba89

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Theorems.Thm_Formalism_FourierDecayAlt_P_G9_hessDet
import Theorems.Thm_Formalism_FourierDecayAlt_P_G9_gaussHessOfMulti
import Theorems.Thm_Formalism_FourierDecayAlt_P_gaussian_multi_integral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G MeasureTheory Matrix Filter Topology
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.G.GaussHess :=
  Formalism.FourierDecayAlt.P.G9.gaussHessOfMulti Formalism.FourierDecayAlt.P.gaussian_multi_integral Formalism.FourierDecayAlt.P.G9.hessDet
end Formalism.FourierDecayAlt.P
