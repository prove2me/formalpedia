-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.En.admissible_length_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:51:41.965059+00:00
-- url     : https://prove2.me/submissions/32de62b6-2e9f-48cc-b5a2-c9fa0a482376

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutEnCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutEnAdmLen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.En
namespace Formalism.FourierDecayAlt.P.CutMP.En
theorem _root_.solution : AdmLen := by
  intro E _ _ _ Wp Wq _ _ _ _ S v a ha
  obtain ⟨w, rfl⟩ := ha
  exact le_trans (Finset.le_sup (f := fun v => (w.1 v).length) (Finset.mem_univ v)) w.2.2
end Formalism.FourierDecayAlt.P.CutMP.En
