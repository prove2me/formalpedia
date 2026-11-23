-- Prove2me | solution 1 for Formalism.MainNotions.DIV.HookProducts.RBTie.dualFrame_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:41:49.75548+00:00
-- url     : https://prove2.me/submissions/9c49b10f-016f-4f10-8f43-08c7ae29d6e7

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
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (hX : IsUnit (X v).det) : (Formalism.HN.dualFrame X v)⁻¹ = (X v)ᵀ := by
  show ((X v)ᵀ)⁻¹⁻¹ = (X v)ᵀ
  exact Matrix.nonsing_inv_nonsing_inv _ (by rw [Matrix.det_transpose]; exact hX)
end Formalism.MainNotions.DIV.HookProducts.RBTie
