-- Prove2me | solution 1 for Formalism.L2.Pj.FundamentalDomainD5.embVec_qsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:16:02.626118+00:00
-- url     : https://prove2.me/submissions/a2b184b9-7a2b-40cf-8d5a-e9c4b1d4f517

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_RhoDotSelf
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_HQsmulRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.FundamentalDomainD5
open NumberField Matrix ComplexConjugate ReciprocityTheory.MultiplicativeHeights
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {r : ℕ}
namespace Formalism.L2.Pj.FundamentalDomainD5
theorem _root_.solution (τ : K →+* ℂ) (q : ℚ) (x : Fin r → K) : embVec τ (q • x) = (q : ℂ) • embVec τ x := by
  ext a
  simp [embVec, Rat.smul_def, map_ratCast]
end Formalism.L2.Pj.FundamentalDomainD5
