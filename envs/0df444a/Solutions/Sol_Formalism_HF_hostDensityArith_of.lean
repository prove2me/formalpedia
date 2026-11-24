-- Prove2me | solution 1 for Formalism.HF.hostDensityArith_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:28.129806+00:00
-- url     : https://prove2.me/submissions/70a2ae88-e849-48f1-a0af-ebece2e5d0c1

import Mathlib
import Definitions.Def_Formalism_DirichletDensity_Statement
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_HostDensityArith
import Theorems.Thm_Formalism_HF_P_hda_log

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Finset Formalism.Q3
noncomputable section
open Formalism Formalism.HF
namespace Formalism.HF
theorem _root_.solution (hAP : Formalism.HF.APLogDensity) (hLD : Formalism.HF.LogToDir) :
    Formalism.HF.HostDensityArith := by
  intro q hq g
  have h := Formalism.HF.P.hda_log hAP q hq g
  exact ⟨h, hLD _ _ h⟩
end Formalism.HF
