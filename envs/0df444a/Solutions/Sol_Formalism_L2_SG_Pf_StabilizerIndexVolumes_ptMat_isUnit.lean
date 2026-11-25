-- Prove2me | solution 1 for Formalism.L2.SG.Pf.StabilizerIndexVolumes.ptMat_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:14:32.070964+00:00
-- url     : https://prove2.me/submissions/414177f6-6d24-4c9d-a728-b14e464ede70

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_Point
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_StabilizerIndexVolumes_PtMatIsUnit
import Theorems.Thm_Formalism_L2_SG_Pf_StabilizerIndexVolumes_ptMat_det

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.StabilizerIndexVolumes
variable {K : Type*} [Field K]
namespace Formalism.L2.SG.Pf.StabilizerIndexVolumes
theorem _root_.solution {n : ℕ} (w : Formalism.MainNotions.S.Point K n) : IsUnit (Formalism.MainNotions.S.ptMat w).det :=
  isUnit_iff_ne_zero.mpr (ptMat_det w)
end Formalism.L2.SG.Pf.StabilizerIndexVolumes
