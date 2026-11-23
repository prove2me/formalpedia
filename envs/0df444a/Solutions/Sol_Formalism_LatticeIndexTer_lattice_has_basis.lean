-- Prove2me | solution 1 for Formalism.LatticeIndexTer.lattice_has_basis
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:41:25.821282+00:00
-- url     : https://prove2.me/submissions/d1f86dfd-92f7-4af6-a80e-9a25e64493a6

import Definitions.Def_Formalism_LogFactorialIndices_StatementIdx
import Definitions.Def_Lemmata_GeneralBFactSecondFurther_Imports
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_IdxBase

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LatticeIndexTer
open Module
open scoped Pointwise
open LatticeIndexLength
namespace Formalism.LatticeIndexTer
theorem _root_.solution : LatBasis := by
  intro O K X _ _ _ _ _ _ _ _ _ _ _ A hA
  have : Submodule.IsLattice K A := ⟨hA.1, hA.2⟩
  let b := Module.Free.chooseBasis O A
  let b' := b.extendOfIsLattice K
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex O A) = finrank K X :=
    (Module.finrank_eq_card_basis b').symm
  refine ⟨b'.reindex (Fintype.equivFinOfCardEq hcard), ?_⟩
  rw [Module.Basis.range_reindex]
  have hr : Set.range b' = A.subtype '' Set.range b := by
    rw [← Set.range_comp]
    ext x
    simp [b']
  rw [hr, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]
end Formalism.LatticeIndexTer
