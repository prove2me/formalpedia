-- Prove2me | solution 1 for Formalism.MainNotions.DIV.HookProducts.RBTie.transpose_isom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:39:03.830729+00:00
-- url     : https://prove2.me/submissions/9472e825-7a43-4fe7-bb6f-5af65eb846c1

import Mathlib
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_SharpRestriction_Divisibility_HookProducts_RBTieFrame
import Definitions.Def_Formalism_SharpRestriction_Divisibility_HookProducts_RBTieOp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix NumberField Module
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.DIV Formalism.MainNotions.DIV.HookProducts Formalism.MainNotions.DIV.HookProducts.RBTie
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {VN VR : Type} [AddCommGroup VN] [Module K VN] [AddCommGroup VR] [Module K VR]
  {ιN ιR : Type} [Fintype ιN] [DecidableEq ιN] [Fintype ιR] [DecidableEq ιR] {d n : ℕ}
namespace Formalism.MainNotions.DIV.HookProducts.RBTie
theorem _root_.solution {ι κ : Type} [Fintype ι] [Fintype κ] (U : Matrix ι κ ℂ) : (Uᵀ)ᴴ * Uᵀ = (U * Uᴴ)ᵀ := by
  rw [Matrix.transpose_mul]
  rfl
end Formalism.MainNotions.DIV.HookProducts.RBTie
