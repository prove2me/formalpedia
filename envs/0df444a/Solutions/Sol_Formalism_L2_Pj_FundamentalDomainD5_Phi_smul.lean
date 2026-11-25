-- Prove2me | solution 1 for Formalism.L2.Pj.FundamentalDomainD5.Phi_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:12:10.742901+00:00
-- url     : https://prove2.me/submissions/e4399bf9-24d4-40f5-a073-aa7a0e74dff2

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_RhoDotSelf
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_HQsmulRight
import Theorems.Thm_Formalism_L2_Pj_FundamentalDomainD5_embVec_smul

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
theorem _root_.solution (σ : ι → K →+* ℂ) (Q : ι → Matrix (Fin r) (Fin r) ℂ) (c : K) (x : Fin r → K) :
    Phi σ Q (c • x) = fun i => σ i c • Phi σ Q x i := by
  funext i
  simp [Phi, embVec_smul, Matrix.mulVec_smul]
end Formalism.L2.Pj.FundamentalDomainD5
