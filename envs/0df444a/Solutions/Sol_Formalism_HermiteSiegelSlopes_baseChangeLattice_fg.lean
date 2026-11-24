-- Prove2me | solution 1 for Formalism.HermiteSiegelSlopes.baseChangeLattice_fg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:12:33.463238+00:00
-- url     : https://prove2.me/submissions/7041623b-dc24-45e9-946a-c39a570f107d

import Definitions.Def_Formalism_MonomialMeanResidues_FilteredDegree
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_MonomialMeanResidues_MonomialMeanProofs_SpanEqTopAndRankOfLinearIndependent
import Theorems.Thm_Formalism_HermiteSiegelSlopes_baseChangeLattice_span_image

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
theorem _root_.solution (M : Submodule (𝓞 F) (ι → F)) (hM : M.FG) : (bcLat (E := E) M).FG := by
  obtain ⟨s, rfl⟩ := hM
  rw [baseChangeLattice_span_image]
  exact Submodule.fg_span (s.finite_toSet.image _)
end Formalism.HermiteSiegelSlopes
