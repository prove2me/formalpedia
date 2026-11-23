-- Prove2me | solution 1 for Formalism.MainNotions.DIV.HookProducts.RBTie.vecAt_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:41:59.105157+00:00
-- url     : https://prove2.me/submissions/148e7b79-535b-48f3-ae8d-0cbbcb55d524

import Mathlib
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_SharpRestriction_Divisibility_HookProducts_RBTieFrame

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
  {V W : Type} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
namespace Formalism.MainNotions.DIV.HookProducts.RBTie
theorem _root_.solution (b : Basis ι K V) (b' : Basis κ K W) (v : InfinitePlace K) (u : V →ₗ[K] W) (x : V) :
    Formalism.HermitianLatticesTheory.vecAt b' v (u x) = (LinearMap.toMatrix b b' u).map v.embedding *ᵥ Formalism.HermitianLatticesTheory.vecAt b v x := by
  funext i
  simp only [Formalism.HermitianLatticesTheory.vecAt, ← LinearMap.toMatrix_mulVec_repr b b' u x, Matrix.mulVec, dotProduct,
    Matrix.map_apply, map_sum, map_mul]
end Formalism.MainNotions.DIV.HookProducts.RBTie
