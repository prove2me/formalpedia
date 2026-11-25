-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdSy.sy_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:50:06.289836+00:00
-- url     : https://prove2.me/submissions/44ecd52b-ccd4-4f70-9cc5-3e040c239e6b

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdLB
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdSy
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdSy_swJ_swJ
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdSy_scaleGenG_scaleGenG
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdSy_unit__mul_51f5e9f25667
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdSy_unit__one_93204f7b6736
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdSy_unit_eq_one_of_corr
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdLB_corr_scaleGenG
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdLB_pullGen_scaleGenG
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_homAt_comp
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_homAt_id
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdLB_unit__homAt_215ffcb691bb
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdLB_unit__injective_2ff253dfce17
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_corr_pullGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_corr_pullGen_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_corr_pullGen_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_corr_pullGen_of_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_corr_trans


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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdSy
open AlgebraicGeometry CategoryTheory Limits MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj NumberField
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G)
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdSy
theorem _root_.solution (hL : t.PP.L.IsLB) {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S}
    {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S} {ph1 ph2 : MvPowerSeries (Fin 3 × Fin d) S}
    {sy : MvPowerSeries (Fin 2 × Fin d) S} {ad : 𝓞 E → MvPowerSeries (Fin 2 × Fin d) S}
    {e : ∀ m, FrTyG t x0 d x m} (hfr : IsFrameG t x0 d x F act ph1 ph2 sy ad e) (m : ℕ) :
    psJet m sy * swJ d m (psJet m sy) = 1 := by
  obtain ⟨u, hu, hc⟩ := hfr.sy m
  have hge := hfr.gen m
  have hhh : (homAt x0 (swJ (S := S) d m)).left ≫ (homAt x0 (swJ d m)).left = 𝟙 _ := by
    rw [← Over.comp_left, homAt_comp, swJ_swJ, homAt_id]
    rfl
  have h1 := DVR.corr_pullGen hc (homAt x0 (swJ (S := S) d m)).left
  rw [FBIdLB.pullGen_scaleGenG] at h1
  have h2 := DVR.corr_trans hL (DVR.corr_pullGen_comp (e m) (homAt x0 (swJ (S := S) d m)).left
    (homAt x0 (swJ (S := S) d m)).left)
    (DVR.corr_trans hL (DVR.corr_pullGen_of_eq (e m) hge _ _ hhh) (DVR.corr_pullGen_id (e m)))
  have h3 := DVR.corr_trans hL h1 (FBIdLB.corr_scaleGenG t h2 _)
  have h4 := DVR.corr_trans hL hc (FBIdLB.corr_scaleGenG t h3 (unitΓ u⁻¹))
  erw [scaleGenG_scaleGenG] at h4
  have h5 := unit_eq_one_of_corr t hL hge h4
  rw [FBIdLB.unitΓ_homAt, ← unitΓ_mul, ← unitΓ_one] at h5
  have h6 := FBIdLB.unitΓ_injective h5
  have h7 : (u : Jet S (Fin 2 × Fin d) m) * swJ d m u = 1 := by
    have h8 := congrArg (fun w : (Jet S (Fin 2 × Fin d) m)ˣ => (w⁻¹ : (Jet S (Fin 2 × Fin d) m)ˣ)) h6
    simp only [inv_one, mul_inv_rev, inv_inv, map_inv] at h8
    have h9 := congrArg Units.val h8
    simp only [Units.val_one, Units.val_mul, Units.coe_map] at h9
    rw [mul_comm]
    exact h9
  rw [← hu]
  exact h7
end Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdSy
