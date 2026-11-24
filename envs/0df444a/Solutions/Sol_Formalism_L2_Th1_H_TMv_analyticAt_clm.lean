-- Prove2me | solution 1 for Formalism.L2.Th1.H.TMv.analyticAt_clm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:28:53.855362+00:00
-- url     : https://prove2.me/submissions/adbe89bf-bac9-4d21-8789-827a53fb3bcb

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_TaylorMvLinear
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_IsogenyFormulaInstance
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LineRestrLinSubst
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
variable {n : Type} [Fintype n]
namespace Formalism.L2.Th1.H.TMv
theorem _root_.solution {m : Type} [Fintype m] {F : (m → ℂ) → ℂ} (L : (n → ℂ) →L[ℂ] (m → ℂ))
    (hF : AnalyticAt ℂ F 0) : AnalyticAt ℂ (fun w => F (L w)) 0 :=
  hF.comp_of_eq (L.analyticAt 0) (map_zero L)
end Formalism.L2.Th1.H.TMv
