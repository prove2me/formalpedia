-- Prove2me | solution 1 for Formalism.L2.Pj.QAt.maxCuspsA_kappa_cc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:34:09.738619+00:00
-- url     : https://prove2.me/submissions/ed56dd7e-8330-499d-8779-bf46ad59bf59

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_MaximalCuspKernels_MaxCuspsPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMeanContinuity
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_MaximalCuspKernels_MaxCuspsPfA

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
open ReciprocityTheory.ChartRestriction.G.FD NumberField Matrix Formalism.L2.Pj.FJ Complex
open scoped ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.QAt
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}
namespace Formalism.L2.Pj.QAt
theorem _root_.solution (X : Data E r) : cc X.κ0 = -X.κ0 := by
  have h2 : cc (2 : E) = 2 := by simp [cc]
  have hm : ∀ x y : E, cc (x * y) = cc x * cc y := fun x y => by simp [cc]
  have hn : ∀ x : E, cc (-x) = -cc x := fun x => by simp [cc]
  rcases X.κ0_xi with h | h
  · rw [h, hm, h2, X.ξ0_im, mul_neg]
  · rw [h, hn, hm, h2, X.ξ0_im, mul_neg]
end Formalism.L2.Pj.QAt
