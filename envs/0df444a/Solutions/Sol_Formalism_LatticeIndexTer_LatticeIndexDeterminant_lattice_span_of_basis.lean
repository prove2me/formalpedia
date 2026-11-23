-- Prove2me | solution 1 for Formalism.LatticeIndexTer.LatticeIndexDeterminant.lattice_span_of_basis
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:41:24.615647+00:00
-- url     : https://prove2.me/submissions/ed4c00c2-259d-43c0-897b-00b0f64e43b4

import Definitions.Def_Formalism_LogFactorialIndices_StatementIdx
import Definitions.Def_Lemmata_DiscreteValuationQuotients_LenQuotSpan
import Definitions.Def_Lemmata_GeneralBFactSecondExtra_Key
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_IdxDet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.LatticeIndexTer
open Module
namespace Formalism.LatticeIndexTer
namespace LatticeIndexDeterminant
theorem _root_.solution : LatBasis := by
  intro O K X _ _ _ _ _ _ _ _ _ _ _ A hA
  have : Module.IsTorsionFree O K :=
    isTorsionFree_iff_algebraMap_injective.mpr (IsFractionRing.injective O K)
  have : Submodule.IsLattice K A := ⟨hA.1, hA.2⟩
  let b := Module.Free.chooseBasis O A
  let bK := b.extendOfIsLattice K
  refine ⟨bK.reindex (bK.indexEquiv (Module.finBasis K X)), ?_⟩
  rw [Basis.range_reindex]
  have hr : Set.range bK = A.subtype '' Set.range b := by
    rw [← Set.range_comp]
    ext x
    simp [bK]
  rw [hr, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]
end LatticeIndexDeterminant
end Formalism.LatticeIndexTer
