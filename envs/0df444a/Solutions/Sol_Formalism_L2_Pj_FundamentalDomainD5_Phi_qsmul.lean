-- Prove2me | solution 1 for Formalism.L2.Pj.FundamentalDomainD5.Phi_qsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:22:05.861045+00:00
-- url     : https://prove2.me/submissions/25a3a161-67f4-4280-9a1f-91905d5cfce3

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_RhoDotSelf
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_HQsmulRight
import Theorems.Thm_Formalism_L2_Pj_FundamentalDomainD5_embVec_qsmul

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
theorem _root_.solution (σ : ι → K →+* ℂ) (Q : ι → Matrix (Fin r) (Fin r) ℂ) (q : ℚ) (x : Fin r → K) :
    Phi σ Q (q • x) = ((q : ℝ) : ℂ) • Phi σ Q x := by
  ext i a
  simp [Phi, embVec_qsmul, Matrix.mulVec_smul, Complex.ofReal_ratCast]
end Formalism.L2.Pj.FundamentalDomainD5
