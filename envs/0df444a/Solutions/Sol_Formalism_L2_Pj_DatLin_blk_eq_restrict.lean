-- Prove2me | solution 1 for Formalism.L2.Pj.DatLin.blk_eq_restrict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:15:52.379498+00:00
-- url     : https://prove2.me/submissions/95e481eb-da45-4ee2-b247-91fe2909f180

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_DatMat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.DatLin
open Matrix Complex
variable {ι n : Type} [Fintype ι] [Fintype n]
namespace Formalism.L2.Pj.DatLin
theorem _root_.solution (N : ι → Matrix n n ℂ) : blk N = (blkC N).restrictScalars ℝ := rfl
end Formalism.L2.Pj.DatLin
