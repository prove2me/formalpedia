-- Prove2me | solution 1 for Formalism.MainNotions.DIV.HookProducts.RBTie.conjT_transpose_isom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:41:49.519582+00:00
-- url     : https://prove2.me/submissions/b9c26c6d-3c1f-4a9e-ba08-f1bab24b338a

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
theorem _root_.solution {ι κ : Type} [Fintype ι] [Fintype κ] (U : Matrix ι κ ℂ) : ((Uᴴ)ᵀ)ᴴ * (Uᴴ)ᵀ = (Uᴴ * U)ᵀ := by
  rw [Matrix.transpose_mul]
  congr 1
  ext i j
  simp
end Formalism.MainNotions.DIV.HookProducts.RBTie
