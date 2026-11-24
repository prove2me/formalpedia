-- Prove2me | solution 1 for Formalism.L2.G.Cmp.gMap_std_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:58:12.234462+00:00
-- url     : https://prove2.me/submissions/49ee208f-d698-4c49-91dc-e493025224c7

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DataG
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_ComparisonMaps_ClsLat
import Theorems.Thm_Formalism_L2_G_Cmp_colSpan_eq
import Theorems.Thm_Formalism_L2_G_Cmp_mem_stdL
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Cmp
open Formalism.MainNotions.G Matrix
variable (W : Type) {Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq] {k : ℕ}
namespace Formalism.L2.G.Cmp
theorem _root_.solution (g : GL (Fin k) Qq) :
    gMap W g (stdL W) ≤ stdL W ↔ ∀ a b, (g : Matrix (Fin k) (Fin k) Qq) a b ∈ (algebraMap W Qq).range := by
  rw [← colSpan_eq]
  constructor
  · intro h a b
    exact (mem_stdL W _).1 (h (Submodule.subset_span ⟨b, rfl⟩)) a
  · intro h
    rw [colSpan, Submodule.span_le]
    rintro _ ⟨c, rfl⟩
    exact (mem_stdL W _).2 fun a => h a c
end Formalism.L2.G.Cmp
