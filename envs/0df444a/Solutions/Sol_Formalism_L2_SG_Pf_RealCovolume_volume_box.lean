-- Prove2me | solution 1 for Formalism.L2.SG.Pf.RealCovolume.volume_box
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:33:51.552106+00:00
-- url     : https://prove2.me/submissions/8339a123-3562-4471-ba96-5f279112aa3a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_RealCovolume
import Theorems.Thm_Formalism_L2_SG_Pf_RealCovolume_volume_boxC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Matrix
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.RealCovolume
variable {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
omit [DecidableEq ι] [DecidableEq κ]
namespace Formalism.L2.SG.Pf.RealCovolume
theorem _root_.solution : volume (Set.pi Set.univ fun _ : ι => Set.pi Set.univ fun _ : κ => boxC) = 1 := by
  simp [volume_pi_pi, volume_boxC]
end Formalism.L2.SG.Pf.RealCovolume
