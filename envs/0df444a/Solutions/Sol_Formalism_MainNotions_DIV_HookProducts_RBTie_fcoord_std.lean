-- Prove2me | solution 1 for Formalism.MainNotions.DIV.HookProducts.RBTie.fcoord_std
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:59:21.344192+00:00
-- url     : https://prove2.me/submissions/a3f56ac7-e49a-48ea-a7fe-b63b30ec6e69

import Mathlib
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_SharpRestriction_Divisibility_HookProducts_RBTieFrame
import Theorems.Thm_Formalism_MainNotions_DIV_HookProducts_RBTie_vecAt_std

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
  {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [Fintype ι] [DecidableEq ι] {d : ℕ}
namespace Formalism.MainNotions.DIV.HookProducts.RBTie
theorem _root_.solution (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (v : InfinitePlace K) (y : Fin d → K) :
    Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K (Fin d)) X v y = (X v)⁻¹ *ᵥ (fun l => v.embedding (y l)) := by
  show (X v)⁻¹ *ᵥ Formalism.HermitianLatticesTheory.vecAt (Pi.basisFun K (Fin d)) v y = _
  rw [vecAt_std]
end Formalism.MainNotions.DIV.HookProducts.RBTie
