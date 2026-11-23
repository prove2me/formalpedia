-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx9.site_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:29:15.522236+00:00
-- url     : https://prove2.me/submissions/423c59f7-fd0e-4ab3-826d-22762a12f06e

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModelWordsAssemble

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Matrix Finset Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.M
open Formalism.FourierDecayAlt.P.Mx9
namespace Formalism.FourierDecayAlt.P.Mx9
theorem _root_.solution (P : Par) (i : Fin P.r) : siteA P i ∈ sitesFrom P 0 := by
  simp [sitesFrom, List.mem_ofFn]
end Formalism.FourierDecayAlt.P.Mx9
