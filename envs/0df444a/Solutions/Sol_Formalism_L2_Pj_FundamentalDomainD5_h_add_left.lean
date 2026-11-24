-- Prove2me | solution 1 for Formalism.L2.Pj.FundamentalDomainD5.h_add_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:15:51.971962+00:00
-- url     : https://prove2.me/submissions/62f0ceb3-667f-469b-8b05-b074648e0d47

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
variable (S : HermForm K r)
namespace Formalism.L2.Pj.FundamentalDomainD5
theorem _root_.solution (x x' y : Fin r → K) : S.h (x + x') y = S.h x y + S.h x' y := by
  simp only [HermForm.h, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
end Formalism.L2.Pj.FundamentalDomainD5
