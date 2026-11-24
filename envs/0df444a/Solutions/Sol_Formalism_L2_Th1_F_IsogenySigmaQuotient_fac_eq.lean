-- Prove2me | solution 1 for Formalism.L2.Th1.F.IsogenySigmaQuotient.fac_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:36:13.511019+00:00
-- url     : https://prove2.me/submissions/12621940-b0c5-43a9-82ad-bc52c73ac1dd

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
theorem _root_.solution (hb : SgStarBasic) (hsa : SgStarAdd) (P z : ℂ) (hP : P ∉ L.lattice)
    (hz : z ∉ L.lattice) :
    fac L P z = sgStar L z ^ 2 * (L.weierstrassP z - L.weierstrassP P) := by
  have hs : sgStar L P ^ 2 ≠ 0 := pow_ne_zero 2 (fun h0 => hP (((hb L).2.2.1 P).1 h0))
  simp only [fac]
  rw [hsa L z P hz hP]
  have := inv_mul_cancel₀ hs
  linear_combination (sgStar L z ^ 2 * (L.weierstrassP z - L.weierstrassP P)) * this
end Formalism.L2.Th1.F.IsogenySigmaQuotient
