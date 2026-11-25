-- Prove2me | solution 1 for Formalism.L2.SG.Pf.RealCovolume.reCo_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:13:47.469428+00:00
-- url     : https://prove2.me/submissions/88e7d73d-7ea7-4c1f-8f2b-d0d7190f86d0

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
namespace Formalism.L2.SG.Pf.RealCovolume
theorem _root_.solution (a : ι → κ → ℂ) (p : ι × κ × Fin 2) :
    reCo a p = if p.2.2 = 0 then (a p.1 p.2.1).re else (a p.1 p.2.1).im := rfl
end Formalism.L2.SG.Pf.RealCovolume
