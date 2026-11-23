-- Prove2me | solution 1 for Formalism.HC.Landau.differentiable_AP
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:56:10.106245+00:00
-- url     : https://prove2.me/submissions/2d0f60c7-25f8-4839-8150-3da5d6717a3c

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ExplicitFormulaErrorOfHostConditions
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaLandau
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_Landau
import Theorems.Thm_Formalism_differentiable_deriv_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Formalism Formalism.HC Formalism.HC.Landau
open Formalism ArithmeticFunction
namespace Formalism.HC.Landau
theorem _root_.solution {P : ℂ → ℂ} (hP : Differentiable ℂ P) (a b : ℂ) : Differentiable ℂ (AP P a b) := by
  have hP' := differentiable_deriv_of hP
  unfold AP
  fun_prop
end Formalism.HC.Landau
