-- Prove2me | solution 1 for Formalism.L2.Pj.FundamentalDomainD5.h_zero_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:14:32.11848+00:00
-- url     : https://prove2.me/submissions/26159e1e-a2d1-4adf-9e8c-05f0a702b34f

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
theorem _root_.solution (y : Fin r → K) : S.h 0 y = 0 := by
  simp [HermForm.h]
end Formalism.L2.Pj.FundamentalDomainD5
