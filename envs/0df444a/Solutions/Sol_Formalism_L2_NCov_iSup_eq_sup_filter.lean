-- Prove2me | solution 1 for Formalism.L2.NCov.iSup_eq_sup_filter
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:37:15.857035+00:00
-- url     : https://prove2.me/submissions/294de0c2-4ac8-4c88-8bd6-cb4141931f01

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactLeftLast_Pz
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoverAlg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.NCov
open Module Module.End
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
namespace Formalism.L2.NCov
theorem _root_.solution {ι : Type*} (p : ι → Submodule K V) (F : Finset ι) (hF : ∀ i, p i ≠ ⊥ → i ∈ F)
    (P : ι → Prop) [DecidablePred P] : (⨆ (i) (_ : P i), p i) = (F.filter P).sup p := by
  apply le_antisymm
  · refine iSup₂_le fun i hi => ?_
    by_cases h : p i = ⊥
    · rw [h]; exact bot_le
    · exact Finset.le_sup (f := p) (Finset.mem_filter.2 ⟨hF i h, hi⟩)
  · exact Finset.sup_le fun i hi => le_iSup₂_of_le (f := fun i (_ : P i) => p i) i
      (Finset.mem_filter.1 hi).2 le_rfl
end Formalism.L2.NCov
