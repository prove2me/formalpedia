-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.opBound_fcoord
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:45.920773+00:00
-- url     : https://prove2.me/submissions/5f3a3fa3-2591-4831-bab7-be37bb80d091

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMaj
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_OpBound
import Theorems.Thm_Formalism_HermitianLatticesTheory_opBound_vecAt_sub
import Theorems.Thm_Formalism_HermitianLatticesTheory_opBound_vecAt_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {K V ι : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (v : InfinitePlace K) (g : V →ₗ[K] V) (y : V) :
    fcoord b X v (g y - y) = (X v)⁻¹ *ᵥ ((matAt b v g - 1) *ᵥ vecAt b v y) := by
  rw [fcoord, opBound_vecAt_sub, opBound_vecAt_map, Matrix.sub_mulVec, Matrix.one_mulVec]
end Formalism.HermitianLatticesTheory
