-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.killAddValCol_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:27:23.734331+00:00
-- url     : https://prove2.me/submissions/795e850b-22a8-41c7-96cc-8c85c920f1bb

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndEncPf
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsExpChart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_KillAdd
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ConstantCoeffPolyAdd
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_KAV_constantCoeff_polyAdd
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_KAV_sum_encP
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_KAV_val_encP
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_KAV_secondOrder_zero

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
namespace Formalism.MainNotions.ModuliIntegralCharts.H1
theorem _root_.solution (h : TB.KillAddSt) : KillAddValColSt := by
  intro E _ _ _ H Dw l c S _ _ _ k n G β hPsi hβ a P hP
  have hK := h S (dL Dw) n (Lt1 Dw) (fun ℓ => Pi.single (ltIdx Dw ℓ) 1) β
    (MvPolynomial.map (algebraMap c.F S) (encP P)) (KAV.secondOrder_zero c hPsi β hβ a n P hP) (-(k : S)) G
  simp only [KAV.constantCoeff_polyAdd (ltIdx Dw) (ltIdx Dw).injective, KAV.sum_encP, KAV.val_encP] at hK
  exact hK
end Formalism.MainNotions.ModuliIntegralCharts.H1
