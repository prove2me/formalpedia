-- Prove2me | solution 1 for Formalism.L2.Th1.H.TMv.lineRestr_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:48:35.850116+00:00
-- url     : https://prove2.me/submissions/886ede19-b824-4e95-935d-baee39db72b7

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_TaylorMvLinear
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_IsogenyFormulaInstance
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LineRestrLinSubst
import Theorems.Thm_Formalism_L2_Th1_H_TMv_lineHom_apply
import Theorems.Thm_Formalism_L2_Th1_F_taylorDeriv
import Theorems.Thm_Formalism_L2_Th1_F_taylorRing


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
open Formalism.L2.Th1.H.TMv
open Formalism.L2.Th1.F (taylor0 taylorRing taylorDeriv)
variable {K : Type*} [CommRing K] {n : Type*} [Finite n]
namespace Formalism.L2.Th1.H.TMv
theorem _root_.solution (v : n → K) (S T : MvPowerSeries n K) :
    lineRestr v (S * T) = lineRestr v S * lineRestr v T := by
  simp only [← lineHom_apply, map_mul]
end Formalism.L2.Th1.H.TMv
