-- Prove2me | solution 1 for Formalism.L2.Th1.F.IsogenySigmaQuotient.fac_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:25:02.227444+00:00
-- url     : https://prove2.me/submissions/827466f5-a418-42d4-aa34-07681e216843

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
theorem _root_.solution (hb : SgStarBasic) (P : ℂ) (hP : P ∉ L.lattice) : fac L P 0 = 1 := by
  have hs : sgStar L P ≠ 0 := fun h0 => hP (((hb L).2.2.1 P).1 h0)
  simp only [fac, zero_add, zero_sub, (hb L).2.1]
  have e : -(sgStar L P ^ 2)⁻¹ * (sgStar L P * -sgStar L P) = (sgStar L P ^ 2)⁻¹ * sgStar L P ^ 2 := by ring
  rw [e, inv_mul_cancel₀ (pow_ne_zero 2 hs)]
end Formalism.L2.Th1.F.IsogenySigmaQuotient
