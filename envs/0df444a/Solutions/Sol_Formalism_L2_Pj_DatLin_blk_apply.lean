-- Prove2me | solution 1 for Formalism.L2.Pj.DatLin.blk_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:18:34.237683+00:00
-- url     : https://prove2.me/submissions/8a749409-5d8b-43c5-84b4-1d5058c8099c

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
theorem _root_.solution (N : ι → Matrix n n ℂ) (u : ι → n → ℂ) (τ : ι) : blk N u τ = N τ *ᵥ u τ := rfl
end Formalism.L2.Pj.DatLin
