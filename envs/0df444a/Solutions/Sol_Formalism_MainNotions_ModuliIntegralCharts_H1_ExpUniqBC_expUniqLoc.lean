-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqBC.expUniqLoc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:59:42.452133+00:00
-- url     : https://prove2.me/submissions/9060add7-070e-4d51-b092-30aea8a2b967

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqTan
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_UnivChartLoc
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqBC
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqBC_br_injective
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqBC_br_mul
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqBC_br_one
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqBC_br_comp
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqTan_trivT
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one__39cc6a6ed057
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_univChartLoc


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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqBC
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqLoc Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqTan
open ReciprocityTheory.ChartRestriction.G.Chart (JetR zR IsUnivChart sp spMap spMap_comp comp_one')
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqBC
theorem _root_.solution : ExpUniqLocSt := by
  intro E _ _ _ H Dw l Xo S _ _ _ x0 d x x' hx hx' ht
  haveI : IsCommMonObj Xo.univ.t.G := Xo.univ.t.semi.comm
  haveI : Smooth Xo.univ.t.G.hom := Xo.univ.t.semi.smooth
  haveI : Smooth (GS Xo.univ.t.G x0).hom := by
    show Smooth (pullback.snd Xo.univ.t.G.hom x0)
    infer_instance
  obtain ⟨n, xu, hxu⟩ := ReciprocityTheory.ChartRestriction.G.Chart.univChartLoc (GS Xo.univ.t.G x0)
  have key : ∀ m, br Xo.univ.t.G x0 (x' m * (x m)⁻¹) = 1 := by
    refine trivT hxu (fun m => br Xo.univ.t.G x0 (x' m * (x m)⁻¹)) ?_ ?_ ?_
    · intro m
      rw [← br_comp]
      congr 1
      simp only [MonObj.comp_mul, GrpObj.comp_inv, hx.1 m, hx'.1 m]
    · intro m
      rw [← br_comp, ← br_comp, ← br_comp, ← br_mul]
      congr 1
      simp only [MonObj.comp_mul, GrpObj.comp_inv]
      rw [hx.2 m, hx'.2 m, _root_.mul_inv, _root_.mul_mul_mul_comm]
    · intro j
      rw [← br_comp, ← br_one (A := DualNumber S)]
      congr 1
      simp only [MonObj.comp_mul, GrpObj.comp_inv, ht j, _root_.mul_inv_cancel]
  funext m
  have h := key m
  rw [← br_one] at h
  exact (_root_.mul_inv_eq_one.1 (br_injective h)).symm
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqBC
