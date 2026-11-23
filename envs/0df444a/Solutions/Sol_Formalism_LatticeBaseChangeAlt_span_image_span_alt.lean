-- Prove2me | solution 1 for Formalism.LatticeBaseChangeAlt.span_image_span_alt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:41:24.36521+00:00
-- url     : https://prove2.me/submissions/9122192b-5277-46b0-b516-1464de987925

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_BetaSesquilinearity
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LinearIndependentOfIsBaseChange

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
namespace Formalism.LatticeBaseChangeAlt
theorem _root_.solution {K K' V V₁ : Type} [Field K] [Field K'] [Algebra K K']
    [AddCommGroup V] [Module K V] [AddCommGroup V₁] [Module K' V₁] [Module K V₁]
    [IsScalarTower K K' V₁] (j : V →ₗ[K] V₁) (s : Set V) :
    Submodule.span K' (j '' (Submodule.span K s : Set V)) = Submodule.span K' (j '' s) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have h1 : j x ∈ Submodule.span K (j '' s) := by
      rw [← Submodule.map_span]
      exact Submodule.mem_map_of_mem hx
    exact Submodule.span_le_restrictScalars K K' _ h1
  · first
    | exact Submodule.span_mono (Set.image_mono Submodule.subset_span)
    | exact Submodule.span_mono (Set.image_subset _ Submodule.subset_span)
end Formalism.LatticeBaseChangeAlt
