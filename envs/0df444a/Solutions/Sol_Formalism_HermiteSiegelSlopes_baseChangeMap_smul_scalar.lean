-- Prove2me | solution 1 for Formalism.HermiteSiegelSlopes.baseChangeMap_smul_scalar
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:05.028328+00:00
-- url     : https://prove2.me/submissions/ebb522c1-3c36-44fa-91ed-6afcfbb39a0d

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
  [Fintype ι] [DecidableEq ι]
namespace Formalism.HermiteSiegelSlopes
theorem _root_.solution (s : F) (x : ι → F) :
    bcMap (E := E) (s • x) = algebraMap F E s • bcMap x := by
  funext i
  simp [bcMap]
end Formalism.HermiteSiegelSlopes
