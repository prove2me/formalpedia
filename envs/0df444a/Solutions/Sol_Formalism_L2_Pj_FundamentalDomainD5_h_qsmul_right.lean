-- Prove2me | solution 1 for Formalism.L2.Pj.FundamentalDomainD5.h_qsmul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:16:01.543593+00:00
-- url     : https://prove2.me/submissions/7dfd3f01-f759-4864-b5e7-3f8cbb5ea306

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_RhoDotSelf
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_HQsmulRight
import Theorems.Thm_Formalism_L2_Pj_FundamentalDomainD5_h_smul_right

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
theorem _root_.solution (q : ℚ) (x y : Fin r → K) : S.h x (q • y) = (q : K) * S.h x y := by
  have hq : q • y = (q : K) • y := by ext a; simp [Rat.smul_def]
  rw [hq, h_smul_right]
end Formalism.L2.Pj.FundamentalDomainD5
