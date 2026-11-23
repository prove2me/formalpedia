-- Prove2me | solution 1 for Formalism.HermiteSiegelSlopes.baseChangeMap_smul_integers
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:58:23.208345+00:00
-- url     : https://prove2.me/submissions/fe6c3867-bc01-4974-ae4b-679aa95e5e78

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
theorem _root_.solution (r : 𝓞 F) (x : ι → F) :
    bcMap (E := E) (r • x) = (algebraMap (𝓞 F) (𝓞 E) r) • bcMap x := by
  funext i
  simp only [bcMap, Pi.smul_apply]
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  rfl
end Formalism.HermiteSiegelSlopes
