-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.gaussian_multi_integral
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:09:57.00652+00:00
-- url     : https://prove2.me/submissions/f436b885-523d-4b1a-86bb-1d6e7242c06c

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Theorems.Thm_Formalism_FourierDecayAlt_P_takagi_factorization
import Theorems.Thm_Formalism_FourierDecayAlt_P_G9_gaussOneDamped
import Theorems.Thm_Formalism_FourierDecayAlt_P_G9_gaussMulti_of

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
theorem _root_.solution : Formalism.FourierDecayAlt.G.GaussMulti :=
  Formalism.FourierDecayAlt.P.G9.gaussMulti_of Formalism.FourierDecayAlt.P.takagi_factorization Formalism.FourierDecayAlt.P.G9.gaussOneDamped
end Formalism.FourierDecayAlt.P
