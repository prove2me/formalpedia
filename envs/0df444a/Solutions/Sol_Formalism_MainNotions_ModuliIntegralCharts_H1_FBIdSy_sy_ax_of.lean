-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdSy.sy_ax_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:20:26.903643+00:00
-- url     : https://prove2.me/submissions/9018858c-fb4a-49b4-8b29-e2037f0db1a1

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdLB
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdSy
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdSy_axJ_swJ
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdSy_psJet_ev_ax
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdSy_unit__one_93204f7b6736
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdJet_psJet_one
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdLB_corr_scaleGenG
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdLB_pullGen_scaleGenG
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdLB_scaleGenG_one
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdLB_scale_eq_of_corr
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_homAt_comp
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermFun_psJet_inj
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdLB_unit__homAt_215ffcb691bb
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdLB_unit__injective_2ff253dfce17
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_corr_pullGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_corr_pullGen_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_corr_pullGen_of_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_corr_symm
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
    {e : ∀ m, FrTyG t x0 d x m} (hfr : IsFrameG t x0 d x F act ph1 ph2 sy ad e)
    (hax : FrAxes t x0 d x e) (b : Bool) :
    ev (n := 1) (if b then ![0, pt S d 0] else ![pt S d 0, 0]) sy = 1 := by
  refine psJet_inj fun m => ?_
  rw [psJet_ev_ax, psJet_one]
  obtain ⟨u, hu, hc⟩ := hfr.sy m
  have hA : ∀ b' : Bool, LB.Gen.Corr t.PP.L _ _ _ _
      (LB.pullGen t.PP.L (cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)]) (cε 2) (e m)
        (homAt x0 (axJ (S := S) d m b')).left) (LB.oneGen t.PP.L) := by
    intro b'
    cases b'
    · exact (hax m).2
    · exact (hax m).1
  have hcomp : (homAt x0 (axJ (S := S) d m b)).left ≫ (homAt x0 (swJ (S := S) d m)).left =
      (homAt x0 (axJ (S := S) d m (!b))).left := by
    rw [← Over.comp_left, homAt_comp, axJ_swJ]
  have h1 := DVR.corr_pullGen hc (homAt x0 (axJ (S := S) d m b)).left
  rw [FBIdLB.pullGen_scaleGenG] at h1
  have h2 := DVR.corr_trans hL (DVR.corr_pullGen_comp (e m) (homAt x0 (swJ (S := S) d m)).left
    (homAt x0 (axJ (S := S) d m b)).left) (DVR.corr_pullGen_of_eq (e m) (hfr.gen m) _ _ hcomp)
  have h3 := DVR.corr_trans hL h1 (FBIdLB.corr_scaleGenG t h2 _)
  have hAB := DVR.corr_trans hL (hA b) (DVR.corr_symm (hA (!b)))
  have h4 := FBIdLB.scale_eq_of_corr t hL hAB (v := 1)
    (by rw [FBIdLB.scaleGenG_one]; exact h3)
  rw [FBIdLB.unitΓ_homAt, ← unitΓ_one] at h4
  have h5 := FBIdLB.unitΓ_injective h4
  have h6 := congrArg (fun w : (Jet S (Fin 1 × Fin d) m)ˣ => ((w⁻¹ : (Jet S (Fin 1 × Fin d) m)ˣ) :
    Jet S (Fin 1 × Fin d) m)) h5
  simp only [inv_one, Units.val_one, map_inv, inv_inv, Units.coe_map] at h6
  rw [← hu]
  exact h6.symm
end Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdSy
