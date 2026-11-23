-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.dual_size_identity
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:58:06.562713+00:00
-- url     : https://prove2.me/submissions/10855bd7-2705-4f36-9088-8db2e8799f52

import Definitions.Def_Formalism_HermitianCurvature_Statement
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualVolumePowerIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Easy_dual_volume_power_identity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset Real
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.DualSizeIdentity := by
  intro ι _ c g rd r i hg hrd
  exact Easy.dual_volume_power_identity ι c g rd r i hg hrd
end Formalism.FourierDecayAlt.P
