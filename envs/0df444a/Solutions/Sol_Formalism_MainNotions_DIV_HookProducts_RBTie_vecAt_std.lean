-- Prove2me | solution 1 for Formalism.MainNotions.DIV.HookProducts.RBTie.vecAt_std
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:41:47.62867+00:00
-- url     : https://prove2.me/submissions/1025f724-db21-4276-8ee8-bf421f9d892b

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
theorem _root_.solution {d : ℕ} (v : InfinitePlace K) (x : Fin d → K) :
    Formalism.HermitianLatticesTheory.vecAt (Pi.basisFun K (Fin d)) v x = fun l => v.embedding (x l) := by
  funext l
  simp [Formalism.HermitianLatticesTheory.vecAt]
end Formalism.MainNotions.DIV.HookProducts.RBTie
