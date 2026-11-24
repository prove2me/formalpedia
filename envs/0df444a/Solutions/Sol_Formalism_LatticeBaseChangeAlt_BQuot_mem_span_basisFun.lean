-- Prove2me | solution 1 for Formalism.LatticeBaseChangeAlt.BQuot.mem_span_basisFun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:33:52.095875+00:00
-- url     : https://prove2.me/submissions/a6be7af7-6826-41b5-a9a5-6e46c14ec52c

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_ReductionQuotient
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_IdxDet
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_MemSpanBasisFun

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LatticeBaseChangeAlt
open Module
open Formalism.LatticeBaseChangeAlt.BQuot
variable {O K V : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V]
  [IsScalarTower O K V]
namespace Formalism.LatticeBaseChangeAlt.BQuot
theorem _root_.solution (n : ℕ) (y : Fin n → K) (h : ∀ i, ∃ a : O, y i = algebraMap O K a) :
    y ∈ Submodule.span O (Set.range (Pi.basisFun K (Fin n))) := by
  choose a ha using h
  have hy : y = ∑ i, a i • Pi.basisFun K (Fin n) i := by
    ext j
    simp [ha, Finset.sum_apply, Pi.single_apply, Algebra.smul_def]
  rw [hy]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
end Formalism.LatticeBaseChangeAlt.BQuot
