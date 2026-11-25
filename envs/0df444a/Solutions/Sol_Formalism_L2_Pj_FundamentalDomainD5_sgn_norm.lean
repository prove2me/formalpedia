-- Prove2me | solution 1 for Formalism.L2.Pj.FundamentalDomainD5.sgn_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:13:23.753242+00:00
-- url     : https://prove2.me/submissions/f64c1a3b-8f0c-4546-bc06-10a44540d476

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
theorem _root_.solution (p : ℕ) (a : Fin r) : ‖sgn p a‖ = 1 := by
  unfold sgn
  split_ifs <;> simp
end Formalism.L2.Pj.FundamentalDomainD5
