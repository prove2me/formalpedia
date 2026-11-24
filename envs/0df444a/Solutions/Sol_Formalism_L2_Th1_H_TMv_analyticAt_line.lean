-- Prove2me | solution 1 for Formalism.L2.Th1.H.TMv.analyticAt_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:46:32.133523+00:00
-- url     : https://prove2.me/submissions/7da4f553-c4dc-4879-809d-b3cfcb40268c

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
theorem _root_.solution {F : (n → ℂ) → ℂ} {t₀ : ℂ} (v : n → ℂ) (hF : AnalyticAt ℂ F (t₀ • v)) :
    AnalyticAt ℂ (fun t : ℂ => F (t • v)) t₀ :=
  hF.comp_of_eq (f := fun t : ℂ => t • v) (analyticAt_id.smul analyticAt_const) rfl
end Formalism.L2.Th1.H.TMv
