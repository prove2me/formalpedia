-- Prove2me | solution 1 for Formalism.LatticeBaseChangeAlt.LatticeIndexBis.span_image_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:35:20.237738+00:00
-- url     : https://prove2.me/submissions/9f5cb7b3-4943-4117-9dd1-56b105546eca

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_BetaSesquilinearity
import Definitions.Def_Formalism_LogFactorialIndices_LogProductFormula
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_SubspaceLatticeIndexSigned
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LatticeIndexBis

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
open Formalism.LatticeBaseChangeAlt.LatticeIndexBis
namespace Formalism.LatticeBaseChangeAlt.LatticeIndexBis
theorem _root_.solution {R S M N : Type} [Ring R] [Ring S] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module S N] (g : M →+ N) (φ : R → S) (h : ∀ r x, g (r • x) = φ r • g x)
    (s : Set M) :
    Submodule.span S (g '' (Submodule.span R s : Set M)) = Submodule.span S (g '' s) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
    | smul r y _ hy => rw [h]; exact Submodule.smul_mem _ _ hy
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)
end Formalism.LatticeBaseChangeAlt.LatticeIndexBis
