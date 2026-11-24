-- Prove2me | solution 1 for Formalism.MainNotions.DIV.HookProducts.RBTie.fcoord_e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:38:59.67637+00:00
-- url     : https://prove2.me/submissions/80b6ff55-4a2f-449a-8803-d125f3a10241

import Mathlib
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_SharpRestriction_Divisibility_HookProducts_RBTieFrame
import Theorems.Thm_Formalism_MainNotions_DIV_HookProducts_RBTie_vecAt_map
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
theorem _root_.solution (b : Basis ι K V) (XA : InfinitePlace K → Matrix ι ι ℂ) (e : (Fin d → K) ≃ₗ[K] V) (v : InfinitePlace K)
    (y : Fin d → K) :
    Formalism.HermitianLatticesTheory.fcoord b XA v (e y) = ((XA v)⁻¹ * cP b e v) *ᵥ (fun l => v.embedding (y l)) := by
  show (XA v)⁻¹ *ᵥ Formalism.HermitianLatticesTheory.vecAt b v (e y) = _
  rw [← Matrix.mulVec_mulVec]
  congr 1
  rw [show e y = e.toLinearMap y from rfl, vecAt_map (Pi.basisFun K (Fin d)) b v e.toLinearMap y, vecAt_std]
  rfl
end Formalism.MainNotions.DIV.HookProducts.RBTie
