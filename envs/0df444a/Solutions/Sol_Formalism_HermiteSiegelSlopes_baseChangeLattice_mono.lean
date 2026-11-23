-- Prove2me | solution 1 for Formalism.HermiteSiegelSlopes.baseChangeLattice_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:58:23.164817+00:00
-- url     : https://prove2.me/submissions/bd147b6c-2f18-4eb9-934b-06423aa882b8

import Definitions.Def_Formalism_MonomialMeanResidues_FilteredDegree
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_MonomialMeanResidues_MonomialMeanProofs_SpanEqTopAndRankOfLinearIndependent

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
theorem _root_.solution {A B : Submodule (𝓞 F) (ι → F)} (h : A ≤ B) :
    bcLat (E := E) A ≤ bcLat B := by
  unfold bcLat
  exact Submodule.span_mono (fun _ ⟨z, hz, hze⟩ => ⟨z, h hz, hze⟩)
end Formalism.HermiteSiegelSlopes
