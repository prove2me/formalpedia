-- Prove2me | solution 1 for Formalism.L2.Pj.FundamentalDomainD5.Phi_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:33:31.348818+00:00
-- url     : https://prove2.me/submissions/c137636e-ebd9-42ed-8406-0ab499d71ed0

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_RhoDotSelf
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_HQsmulRight
import Theorems.Thm_Formalism_L2_Pj_FundamentalDomainD5_Phi_add

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
theorem _root_.solution (σ : ι → K →+* ℂ) (Q : ι → Matrix (Fin r) (Fin r) ℂ) {κ : Type} (s : Finset κ)
    (x : κ → Fin r → K) : Phi σ Q (∑ j ∈ s, x j) = ∑ j ∈ s, Phi σ Q (x j) := by
  exact map_sum (AddMonoidHom.mk' (Phi σ Q) (Phi_add σ Q)) x s
end Formalism.L2.Pj.FundamentalDomainD5
