-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.jointSpan_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:56:55.887418+00:00
-- url     : https://prove2.me/submissions/af94593d-8fb1-4731-8787-be8d6a9a079d

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open Matrix
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ}
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (F F' : FlagD H r) {c : K} (hz : F'.z - c • F.z ∈ F.X ⊔ F'.X) :
    V0 F F' = (F.X ⊔ F'.X) ⊔ K ∙ F.z := by
  unfold Formalism.HermitianLatticeCounting.S6.V0
  apply le_antisymm
  · refine sup_le le_sup_left ?_
    rw [Submodule.span_le]
    intro s hs
    rcases hs with rfl | hs
    · exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
    · rw [Set.mem_singleton_iff.1 hs, ← sub_add_cancel F'.z (c • F.z)]
      exact Submodule.add_mem _ (Submodule.mem_sup_left hz)
        (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)))
  · exact sup_le_sup_left (Submodule.span_mono (Set.singleton_subset_iff.2 (Set.mem_insert _ _))) _
end Formalism.HermitianLatticeCounting.P
