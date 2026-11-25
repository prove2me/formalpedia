-- Prove2me | solution 1 for Formalism.L2.SG.Pf.RealCovolume.isAddHaar_vol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:18:34.799118+00:00
-- url     : https://prove2.me/submissions/3e8aa5bc-0bfb-4044-b0c5-92c72bef678c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_RealCovolume

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
theorem _root_.solution : (volume : Measure (ι → κ → ℂ)).IsAddHaarMeasure := by
  first
  | infer_instance
  | exact Measure.pi.isAddHaarMeasure _
end Formalism.L2.SG.Pf.RealCovolume
