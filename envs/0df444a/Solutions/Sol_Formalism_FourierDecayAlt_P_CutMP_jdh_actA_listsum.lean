-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.jdh_actA_listsum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:25:05.016583+00:00
-- url     : https://prove2.me/submissions/66e6b007-6b18-4b14-90dd-3b52bff53558

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJD
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGaugeCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJDHat
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_jdh_actA_zeroR
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_jdh_actA_addR

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP
open NumberField
noncomputable section
variable (P : M.Par)
namespace Formalism.FourierDecayAlt.P.CutMP
theorem _root_.solution {ι : Type} (a : MA.A P (MA.DQ P)) (l : List ι) (g : ι → M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P a (l.map g).sum = (l.map fun i => MA.actA P a (g i)).sum := by
  induction l with
  | nil => simp only [List.map_nil, List.sum_nil]; exact jdh_actA_zeroR P a
  | cons i l ih => simp only [List.map_cons, List.sum_cons]; rw [jdh_actA_addR, ih]
end Formalism.FourierDecayAlt.P.CutMP
