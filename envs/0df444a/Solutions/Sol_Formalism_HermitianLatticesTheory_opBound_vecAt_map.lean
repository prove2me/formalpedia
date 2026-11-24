-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.opBound_vecAt_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:54:01.406412+00:00
-- url     : https://prove2.me/submissions/553df15c-70be-408d-9441-07ff3ef4e2c7

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMaj
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_OpBound

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
theorem _root_.solution (b : Module.Basis ι K V) (v : InfinitePlace K) (g : V →ₗ[K] V) (y : V) :
    vecAt b v (g y) = matAt b v g *ᵥ vecAt b v y := by
  funext i
  simp only [vecAt, matAt]
  rw [← LinearMap.toMatrix_mulVec_repr b b g y, RingHom.map_mulVec]
  rfl
end Formalism.HermitianLatticesTheory
