-- Prove2me | solution 1 for Formalism.HermiteSiegelSlopes.baseChangeLattice_sup
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:03.680848+00:00
-- url     : https://prove2.me/submissions/78813478-7f7a-4f60-8342-423d506bd1d8

import Definitions.Def_Formalism_MonomialMeanResidues_FilteredDegree
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_MonomialMeanResidues_MonomialMeanProofs_SpanEqTopAndRankOfLinearIndependent
import Theorems.Thm_Formalism_HermiteSiegelSlopes_baseChangeLattice_span

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Finset
noncomputable section
open Formalism Formalism.HermiteSiegelSlopes
open Formalism.HN
open scoped nonZeroDivisors
open IsDedekindDomain
variable {F E ι : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace Formalism.HermiteSiegelSlopes
theorem _root_.solution (A B : Submodule (𝓞 F) (ι → F)) :
    bcLat (E := E) (A ⊔ B) = bcLat A ⊔ bcLat B := by
  have key : A ⊔ B = Submodule.span (𝓞 F) ((A : Set (ι → F)) ∪ B) := by
    rw [Submodule.span_union, Submodule.span_eq, Submodule.span_eq]
  rw [key, baseChangeLattice_span, Set.image_union, Submodule.span_union]
  rfl
end Formalism.HermiteSiegelSlopes
