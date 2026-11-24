-- Prove2me | solution 1 for Formalism.L2.Th1.F.IsogenySigmaQuotient.herm_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:25:03.068867+00:00
-- url     : https://prove2.me/submissions/1d2a1850-9f1d-4c57-8c28-15ecb709bf76

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_IsogenySigma

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.IsogenySigmaQuotient
variable (L : PeriodPair)
variable (α : ℂ) (S : Finset ℂ)
namespace Formalism.L2.Th1.F.IsogenySigmaQuotient
theorem _root_.solution (z ω : ℂ) : herm L (α * z) (α * ω) = (Complex.normSq α : ℂ) * herm L z ω := by
  simp only [herm, map_mul]; rw [← Complex.mul_conj]; ring
end Formalism.L2.Th1.F.IsogenySigmaQuotient
