-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2.isFrame_tw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:36:27.296805+00:00
-- url     : https://prove2.me/submissions/a0b0321e-2cff-4c0e-a112-e7fe4b6b7c7f

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFix
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdSy
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_MulGenScaleRight
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrFix2_scaleGen_eq
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrFix2_mulGen_scale_right
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrFix2_pe_tw
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrFix2_tw_isGen
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdLB_corr_scaleGenG
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdLB_invGen_scaleGenG
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdLB_mulGen_scaleGenG
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdLB_scaleGenG_one
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdSy_scaleGenG_scaleGenG
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdSy_unit__mul_51f5e9f25667
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_sub


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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open MvPolynomial (X)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (d : ℕ)
variable (x : ∀ m, jO y d m 1 ⟶ Xo.univ.t.G)
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2
theorem _root_.solution [StarRing (𝓞 E)] {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S}
    {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S}
    {ph1 ph2 : MvPowerSeries (Fin 3 × Fin d) S} {sy : MvPowerSeries (Fin 2 × Fin d) S}
    {ad : 𝓞 E → MvPowerSeries (Fin 2 × Fin d) S} (e : ∀ m, FrTy y d x m) (T : ∀ m, (Jet S (Fin 2 × Fin d) m)ˣ)
    (hF : IsFrame y d x F act ph1 ph2 sy ad e)
    (hm1 : ∀ m, sub d m ![fun j => psIn d m ![0, 1] (F j), fun j => X ((2 : Fin 3), j)] (T m) =
      sub d m ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)] (T m) *
        sub d m ![fun j => X ((1 : Fin 3), j), fun j => X ((2 : Fin 3), j)] (T m))
    (hm2 : ∀ m, sub d m ![fun j => X ((0 : Fin 3), j), fun j => psIn d m ![1, 2] (F j)] (T m) =
      sub d m ![fun j => X ((0 : Fin 3), j), fun j => X ((1 : Fin 3), j)] (T m) *
        sub d m ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)] (T m))
    (hs : ∀ m, sub d m ![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)] (T m) = T m)
    (hb : ∀ m a, sub d m ![fun j => psIn d m ![0] (act a j), fun j => X ((1 : Fin 2), j)] (T m) =
      sub d m ![fun j => X ((0 : Fin 2), j), fun j => psIn d m ![1] (act (H.bar a) j)] (T m)) :
    IsFrame y d x F act ph1 ph2 sy ad (tw y d x e T) := by
  refine ⟨fun m => tw_isGen y d x e T m (hF.gen m), fun m => ?_, fun m => ?_, fun m => ?_, fun a => ?_⟩
  · obtain ⟨u, hu, hc⟩ := hF.ph1 m
    refine ⟨u, hu, ?_⟩
    rw [pe_tw, pe_tw, pe_tw, FBIdLB.invGen_scaleGenG, FBIdLB.invGen_scaleGenG, FBIdLB.mulGen_scaleGenG,
      FBIdLB.mulGen_scaleGenG, hm1 m, FBIdSy.unitΓ_mul, ← _root_.mul_inv, _root_.mul_inv_cancel, FBIdLB.scaleGenG_one]
    exact hc
  · obtain ⟨u, hu, hc⟩ := hF.ph2 m
    refine ⟨u, hu, ?_⟩
    rw [pe_tw, pe_tw, pe_tw, FBIdLB.invGen_scaleGenG, FBIdLB.invGen_scaleGenG, FBIdLB.mulGen_scaleGenG,
      FBIdLB.mulGen_scaleGenG, hm2 m, FBIdSy.unitΓ_mul, ← _root_.mul_inv, _root_.mul_inv_cancel, FBIdLB.scaleGenG_one]
    exact hc
  · obtain ⟨u, hu, hc⟩ := hF.sy m
    refine ⟨u, hu, ?_⟩
    have key := FBIdLB.corr_scaleGenG Xo.univ.t hc (unitΓ (T m))
    have eR : scaleGen _ _ (unitΓ u⁻¹) (pe y d x (tw y d x e T) m
        ![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)]) =
        scaleGenG Xo.univ.t _ _ (unitΓ (T m)) (scaleGen _ _ (unitΓ u⁻¹)
          (pe y d x e m ![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)])) := by
      rw [pe_tw, hs m, scaleGen_eq, scaleGen_eq, FBIdSy.scaleGenG_scaleGenG, FBIdSy.scaleGenG_scaleGenG,
        _root_.mul_comm]
    rw [eR]
    exact key
  · obtain ⟨wL, hwL, h⟩ := hF.ad a
    refine ⟨wL, hwL, fun m => ?_⟩
    obtain ⟨u, hu, hc⟩ := h m
    refine ⟨u, hu, ?_⟩
    have key := FBIdLB.corr_scaleGenG Xo.univ.t hc
      (unitΓ (sub d m ![fun j => X ((0 : Fin 2), j), fun j => psIn d m ![1] (act (H.bar a) j)] (T m)))
    rw [pe_tw, pe_tw, hb m a, mulGen_scale_right, scaleGen_eq, FBIdSy.scaleGenG_scaleGenG,
      _root_.mul_comm, ← FBIdSy.scaleGenG_scaleGenG]
    exact key
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2
