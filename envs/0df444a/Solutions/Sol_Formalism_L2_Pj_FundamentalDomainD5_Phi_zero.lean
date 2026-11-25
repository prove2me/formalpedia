-- Prove2me | solution 1 for Formalism.L2.Pj.FundamentalDomainD5.Phi_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:12:17.313489+00:00
-- url     : https://prove2.me/submissions/4980c5e8-4bfd-400e-9107-978b666bc78f

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
theorem _root_.solution (σ : ι → K →+* ℂ) (Q : ι → Matrix (Fin r) (Fin r) ℂ) : Phi σ Q (0 : Fin r → K) = 0 := by
  have h : ∀ i, embVec (σ i) (0 : Fin r → K) = 0 := fun i => by ext a; simp [embVec]
  ext i a
  simp [Phi, h]
end Formalism.L2.Pj.FundamentalDomainD5
