-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.gauge_section_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:01:29.619738+00:00
-- url     : https://prove2.me/submissions/b46bd7a1-fd6d-45e6-a235-0a3a7c56315a

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheSection
import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheSectionStab
import Theorems.Thm_Formalism_FourierDecayAlt_P_TheSecStab_theSection_csec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
theorem _root_.solution : SecExists := by
  intro Wp Wq _ _ _ _ _ _ P Bs _ hk
  exact ⟨Formalism.FourierDecayAlt.P.TheSec.theSection P.k P.r Bs.z Bs.z',
    Formalism.FourierDecayAlt.P.TheSecStab.theSection_csec (by omega) Bs.z_mem Bs.z'_mem Bs.T_pos Bs.T'_pos⟩
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
